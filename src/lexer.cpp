#include <iostream>
#include <sstream>
#include <fstream>
#include <array>
#include <set>
#include <map>
#include <cassert>
#include "lexer.h"
#include "core/common.h"


namespace Lexer {

  string cutFirstCodepoint(const string& s) {
    if (s.empty()) return s;
    size_t pos = 1;
    for (; pos < s.size(); pos++) {
      unsigned char c = s[pos];
      if ((c & 0b11000000) != 0b10000000) break;
    }
    return s.substr(pos);
  }

  void NFALexer::ignoreNextCodepoint() { rest = cutFirstCodepoint(rest); }
  void DFALexer::ignoreNextCodepoint() { rest = cutFirstCodepoint(rest); }

  // Directly run NFA
  optional<pair<size_t, TokenID>> NFALexer::run(const string& str) const {
    optional<pair<size_t, TokenID>> res = nullopt;
    vector<State> s;
    vector<bool> v(table.size(), false);

    // A helper function
    auto closure = [&v, this] (vector<State>& s) {
      // Expand to epsilon closure (using DFS)
      vector<State> stk = s;
      while (!stk.empty()) {
        State x = stk.back(); stk.pop_back();
        for (auto [cc, u]: table[x].tr) if (cc == 0 && !v[u]) {
          s.push_back(u);
          stk.push_back(u);
          v[u] = true;
        }
      }
      // Reset v[] to false
      for (State x: s) v[x] = false;
    };

    s.push_back(initial);
    v[initial] = true;
    closure(s);
    for (size_t i = 0; i < str.size(); i++) {
      unsigned char c = str[i];
      // Move one step
      vector<State> t;
      for (State x: s) for (auto [cc, u]: table[x].tr) if (cc == c && !v[u]) {
        t.push_back(u);
        v[u] = true;
      }
      closure(t);
      s.swap(t);
      // Update result if reaches accepting state
      // Patterns with smaller IDs have higher priority
      optional<TokenID> curr = nullopt;
      for (State x: s) if (table[x].ac) {
        if (!curr || curr.value() > table[x].ac.value()) curr = table[x].ac;
      }
      // Update longest match, if applicable
      if (curr) res = { i + 1, curr.value() };
      // Exit if no more possible matches
      if (s.empty()) break;
    }
    return res;
  }

  optional<Token> NFALexer::getNextToken() {
    auto opt = run(rest);
    if (!opt) return nullopt;
    auto [len, id] = opt.value();
    Token res{ id, rest.substr(0, len) };
    rest = rest.substr(len);
    return res;
  }

  using std::array;
  using std::set;
  using std::map;

  // Function object for the DFA construction from NFA
  class PowersetConstruction {
  public:
    const NFALexer& nfa;
    DFALexer* dfa;
    map<set<NFALexer::State>, DFALexer::State> mp;

    PowersetConstruction(const NFALexer& nfa, DFALexer* dfa): nfa(nfa), dfa(dfa), mp() {}
    PowersetConstruction(const PowersetConstruction&) = delete;
    PowersetConstruction& operator= (const PowersetConstruction&) = delete;

    // We must use sets (for comparing states) nevertheless, so v[] is not needed
    void closure(set<NFALexer::State>& s) const {
      // Expand to epsilon closure (using DFS)
      vector<NFALexer::State> stk(s.begin(), s.end());
      while (!stk.empty()) {
        NFALexer::State nx = stk.back(); stk.pop_back();
        for (auto [cc, nu]: nfa.table[nx].tr) if (cc == 0 && !s.contains(nu)) {
          s.insert(nu);
          stk.push_back(nu);
        }
      }
    };

    #define node(x_, s_) \
      x_ = mp[s_] = dfa->table.size(); \
      dfa->table.emplace_back()
    #define trans(s_, c_, t_) \
      dfa->table[s_].has[c_] = true; \
      dfa->table[s_].tr[c_] = t_

    void dfs(DFALexer::State x, const set<NFALexer::State>& s) {
      // Check if `s` contains accepting states
      optional<TokenID> curr;
      for (auto ns: s) {
        auto opt = nfa.table[ns].ac;
        if (opt && (!curr || curr.value() > opt.value())) curr = opt;
      }
      dfa->table[x].ac = curr;
      // Compute transitions
      for (unsigned int c = 0x01; c <= 0xFF; c++) {
        // Compute u
        set<NFALexer::State> t;
        for (auto nx: s) for (auto [cc, nu]: nfa.table[nx].tr) {
          if (cc == c && !t.contains(nu)) t.insert(nu);
        }
        if (t.empty()) continue;
        closure(t);
        // Look at u:
        auto it = mp.find(t);
        if (it != mp.end()) {
          // Already seen
          trans(x, c, it->second);
        } else {
          // Haven't seen before, create new DFA node and recurse
          node(DFALexer::State u, t);
          trans(x, c, u);
          dfs(u, t);
        }
      }
    }

    void operator() () {
      set<NFALexer::State> s = { nfa.initial };
      closure(s);
      node(dfa->initial, s);
      dfs(dfa->initial, s);
    }

    #undef node
    #undef trans
  };

  DFALexer::DFALexer(const NFALexer& nfa): table(), initial(0), rest() {
    PowersetConstruction(nfa, this)();
  }

  // Function object for the DFA state minimization
  //   See: https://en.wikipedia.org/wiki/DFA_minimization#Hopcroft's_algorithm
  //   See: https://en.wikipedia.org/wiki/Partition_refinement
  // Pre: the TokenIDs in accepting states are small nonnegative integers.
  // (They are directly used as initial partition IDs; I am too lazy so I didn't make a map.)
  class PartitionRefinement {
  public:
    typedef DFALexer::State State;
    typedef DFALexer::Entry Entry;
    struct List { List *l, *r; State x; };

    Allocator<List> pool;
    DFALexer* dfa;

    struct Class { size_t size; List* head; bool isDist; };
    struct Identity { size_t cl; List* ptr; };

    // Ephemeral states (I put these here only to unclutter the main function...)
    vector<vector<pair<unsigned char, State>>> rev; // Reverse edges
    vector<Class> cl;                   // Classes (size, pointer to head, is used as distinguisher set)
    vector<Identity> id;                // Identities (class index, pointer to list)
    vector<size_t> dist;                // Indices of classes used as distinguisher sets
    vector<State> dom[0x100];           // Character -> domain
    vector<vector<State>> interStates;  // Class index -> list of intersecting states

    PartitionRefinement(DFALexer* dfa):
      pool(), dfa(dfa), rev(), cl(), id(), dist(), dom(), interStates() {}
    PartitionRefinement(const PartitionRefinement&) = delete;
    PartitionRefinement& operator= (const PartitionRefinement&) = delete;

    // Add DFA node `x` to class `i`, overwriting `id[x]`
    void add(State x, size_t i) {
      cl[i].size++;
      List* l = cl[i].head, * r = l->r;
      List* curr = pool.push_back({ l, r, x });
      l->r = r->l = curr;
      id[x] = { i, curr };
    }

    // Remove DFA node `x` from its class, as indicated in `id[x]`
    void remove(State x) {
      auto [i, curr] = id[x];
      List* l = curr->l, * r = curr->r;
      l->r = r; r->l = l;
      cl[i].size--;
    }

    // Create new class and return its ID (always = partition.size() - 1, just for convenience)
    size_t newClass() {
      List* head = pool.push_back({ nullptr, nullptr, 0 });
      head->l = head->r = head;
      size_t index = cl.size();
      cl.emplace_back(0, head, false);
      return index;
    }

    void operator() () {
      auto& table = dfa->table;
      auto& initial = dfa->initial;

      // This implementation does not explicitly add the dead state; instead it assumes that
      // all nonexistent transititions point to an "imaginary" or "canonical" dead state.
      // (It magically works! And this looks somewhat less verbose than my original implementation
      //  with an explicit dead state, so I kept this...)
      size_t n = table.size();
      TokenID numTokens = 0;
      for (size_t i = 0; i < n; i++) if (table[i].ac) {
        numTokens = std::max(numTokens, table[i].ac.value() + 1);
      }

      // Process reverse edges (arcs)
      rev.clear(); rev.resize(n);
      for (size_t i = 0; i < n; i++) {
        for (unsigned int c = 0x01; c <= 0xFF; c++) if (table[i].has[c]) {
          rev[table[i].tr[c]].emplace_back(c, i);
        }
      }

      // Initial partition (numTokens + 1 classes)
      // The last class should be seen as "containing the imaginary dead state"
      // (When it splits, the "imaginary dead state" goes with the non-distinguisher part...
      //  But if both splits are used as distinguishers, the i.d.s. is then seen as distinguished...
      //  And it will become possible for some "concrete dead state" to coexist with i.d.s. then...)
      cl.clear();
      for (size_t i = 0; i <= numTokens; i++) newClass();
      id.clear(); id.resize(n);
      for (size_t i = 0; i < n; i++) {
        if (table[i].ac) add(i, table[i].ac.value());
        else             add(i, numTokens);
      }

      // All classes except the last one (just not needed) are used as initial distinguisher sets
      dist.clear();
      for (size_t i = 0; i < numTokens; i++) {
        dist.push_back(i);
        cl[i].isDist = true;
      }

      interStates.clear();
      while (!dist.empty()) {
        size_t curr = dist.back();
        dist.pop_back();
        cl[curr].isDist = false;

        // Calculate the domain sets for all c's
        for (unsigned int c = 0x01; c <= 0xFF; c++) dom[c].clear();
        for (const List* p = cl[curr].head->r; p != cl[curr].head; p = p->r) {
          // "Examine transitions" - this occurs a limited number of times, see below
          // Note that the total size of dom[] is bounded by this
          for (auto [c, s]: rev[p->x]) dom[c].push_back(s);
        }

        for (unsigned int c = 0x01; c <= 0xFF; c++) {
          // Inner loop: time complexity should be O(size of dom[c])
          // Pre: all entries of interStates[] are empty
          interStates.resize(cl.size());
          for (State x: dom[c]) interStates[id[x].cl].push_back(x);
          for (State x: dom[c]) {
            size_t i = id[x].cl;

            // If intersection has been processed before...
            if (i >= interStates.size() || interStates[i].empty()) continue;
            // If difference is empty...
            if (interStates[i].size() == cl[i].size) {
              interStates[i].clear();
              continue;
            }

            // Create a new class for the "intersection"
            size_t interi = newClass();
            // Add elements into it...
            for (State y: interStates[i]) {
              remove(y);
              add(y, interi);
            }
            // The original class now becomes the "set difference"!
            // Avoid processing multiple times, also does the clearing
            interStates[i].clear();

            // See which splits will be used as distinguisher sets
            if (cl[i].isDist || cl[interi].size <= cl[i].size) {
              dist.push_back(interi);
              cl[interi].isDist = true;
            } else { // (!cl[i].isDist && cl[i].size < cl[interi].size)
              dist.push_back(i);
              cl[i].isDist = true;
            }
          }
          // Post: all interStates[] are empty at this time
        }
      }

      // Rebuild `table` and `initial`
      vector<Entry> newTable(cl.size());
      State newInitial = id[initial].cl;

      for (size_t i = 0; i < table.size(); i++) {
        State srci = id[i].cl;
        for (unsigned int c = 0x01; c <= 0xFF; c++) if (table[i].has[c]) {
          State dsti = id[table[i].tr[c]].cl;
          newTable[srci].has[c] = true;
          newTable[srci].tr[c] = dsti;
        }
        if (table[i].ac) newTable[srci].ac = table[i].ac;
      }

      table.swap(newTable);
      initial = newInitial;

      /*
      * ===== A hand-wavey argument for correctness =====
      * (This assumes that an explicit dead state is constructed; justification for the i.d.s. is omitted here)
      *
      * Different classes -> different behaviors: by induction.
      * Different behaviors -> different classes:
      *   (Lemma: for any two disjoint classes, a "distinguisher of them" must have existed.)
      *   For any states s, t arriving at different accepting states after taking the path a:
      *     Let the intermediate states be i1 ... in and j1 ... jn.
      *     For any k, some "distinguisher of ik and jk" must have existed: by induction.
      *       Initial (k = n): in and jn are different non/accepting values so they are in different initial partitions...
      *       Step (k < k' - 1):
      *         By the time the "distinguisher of ik' and jk'" is current,
      *         either ik and jk in the same class (it then get splitted, one of the split becomes distinguisher),
      *         or they are in different classes (by Lemma).
      *     So i1 and j1 (s and t) must be in different classes
      *     (All distinguishers are classes; all classes are disjoint).
      *
      * ===== A hand-wavey argument for time complexity =====
      * (Lemma: if a class is ever used ("currented") as a distinguisher,
      *         the only overlapping distinguishers ever "currented" must come from its splits;
      *         but each split that can possibly be used as a distinguisher must ≤ half of the original size.)
      * Associate each "examination of transition" with the current distinguisher set.
      *   The destination state `dst` of the transition must be in the distinguisher set!
      *   This set then splits, any split "ever used as distinguisher" that contains `dst` must ≤ half of the original size.
      *   So each transition may only be examined O(log n) times...
      * Overall: O(|Σ|n log n)
      */

      // How could a human ever come up with such an algorithm... 这玩意是人能发明出来的吗
    }
  };

  void DFALexer::optimize() {
    PartitionRefinement(this)();
  }

  // Run DFA
  optional<pair<size_t, TokenID>> DFALexer::run(const string& str) const {
    optional<pair<size_t, TokenID>> res = nullopt;
    State s = initial;
    for (size_t i = 0; i < str.size(); i++) {
      unsigned char c = str[i];
      if (!table[s].has[c]) break;
      s = table[s].tr[c];
      // Update result if reaches accepting state
      auto curr = table[s].ac;
      if (curr) res = { i + 1, curr.value() };
    }
    return res;
  }

  optional<Token> DFALexer::getNextToken() {
    auto opt = run(rest);
    if (!opt) return nullopt;
    auto [len, id] = opt.value();
    Token res{ id, rest.substr(0, len) };
    rest = rest.substr(len);
    return res;
  }
}


using std::string;
using std::optional, std::make_optional, std::nullopt;
using std::cin, std::cout, std::endl;
using Lexer::Token, Lexer::TokenID;
using Lexer::NFALexer, Lexer::DFALexer;

class TestLexer: public NFALexer {
public:
  enum ETokenID: TokenID {
    BLANK = 0, LINE_COMMENT, BLOCK_COMMENT, PREPROCESSOR,
    NATURAL, STRING, DELIMITER, OPERATOR, KEYWORD, IDENTIFIER
  };

  TestLexer(): NFALexer() {
    addPattern(ETokenID::BLANK,
      star(ch({ ' ', '\t', '\n', '\v', '\f', '\r' })));
    addPattern(ETokenID::LINE_COMMENT,
      concat(word("//"), star(except({ '\r', '\n' }))));
    addPattern(ETokenID::BLOCK_COMMENT,
      concat(word("/*"),
        star(concat(star(except({ '*' })), plus(ch({ '*' })), except({ '/' }))),
                    star(except({ '*' })), plus(ch({ '*' })), ch({ '/' })));
    addPattern(ETokenID::PREPROCESSOR,
      concat(ch({ '#' }), star(except({ '\r', '\n' }))));
    addPattern(ETokenID::NATURAL,
      alt({ star(range('0', '9')),
            concat(ch({ '0' }), ch({ 'x', 'X' }), star(alt({ range('0', '9'), range('a', 'f'), range('A', 'F') }))) }));
    addPattern(ETokenID::STRING,
      concat(ch({ '"' }), star(alt({ except({ '"', '\\' }), concat(ch({ '\\' }), ch({ '"', '\\' })) })), ch({ '"' })));
    addPattern(ETokenID::DELIMITER,
      ch({ '{', '}', ';' }));
    addPattern(ETokenID::OPERATOR,
      alt({ ch({ '+', '-', '*', '/', '\\', '%', '&', '(', ')', ',', ':', '?', '[', ']', '^', '|', '<', '>', '=', '`' }),
            word("->"), word("<->"), word("↑"), word("=>"), word(":="), word("::"), word(":<->") }));
    addPattern(ETokenID::KEYWORD,
      alt({ word("any"), word("anyfunc"), word("anypred"), word("assume"), word("def"), word("idef"), word("undef"),
            word("proof"), word("by"), word("name"), word("namespace"), word("private"), word("public"),
            word("and"), word("or"), word("implies"), word("not"), word("iff"), word("true"), word("false"), word("eq"),
            word("forall"), word("exists"), word("unique"), word("forallfunc"), word("forallpred") }));
    addPattern(ETokenID::IDENTIFIER,
      concat(
        alt({ range('a', 'z'), range('A', 'Z'), ch({ '_' }), utf8segment() }),
        star(alt({ range('a', 'z'), range('A', 'Z'), range('0', '9'), ch({ '_', '\'', '.' }), utf8segment() }))));
  }

  optional<Token> getNextToken() override {
    auto res = NFALexer::getNextToken();
    while (res && res.value().first == BLANK) res = NFALexer::getNextToken();
    return res;
  }

  static string printToken(const Token& tok) {
    switch (tok.first) {
      case BLANK:         return "Blank of length " + std::to_string(tok.second.size());
      case LINE_COMMENT:  return "Line comment [" + tok.second + "]";
      case BLOCK_COMMENT: return "Block comment [" + tok.second + "]";
      case PREPROCESSOR:  return "Preprocessor [" + tok.second + "]";
      case NATURAL:       return "Natural [" + tok.second + "]";
      case STRING:        return "String [" + tok.second + "]";
      case DELIMITER:     return "Delimiter [" + tok.second + "]";
      case OPERATOR:      return "Operator [" + tok.second + "]";
      case KEYWORD:       return "Keyword [" + tok.second + "]";
      case IDENTIFIER:    return "Identifier [" + tok.second + "]";
      default:            return "Unknown [" + tok.second + "]";
    }
  }
};

// See: https://stackoverflow.com/questions/116038/how-do-i-read-an-entire-file-into-a-stdstring-in-c
string readFile(std::ifstream& in) {
  std::ostringstream sstr;
  sstr << in.rdbuf();
  return sstr.str();
}

int main() {
  TestLexer nfa;
  DFALexer test(nfa);

  cout << nfa.table.size() << endl;
  cout << test.table.size() << endl;
  test.optimize();
  cout << test.table.size() << endl;

  std::ifstream in("test.txt");
  test << readFile(in);
  in.close();

  // Avoid cutting UTF-8 segments
  auto cutoff = [] (const string& s, size_t pos) {
    for (; pos < s.size(); pos++) {
      unsigned char c = s[pos];
      if ((c & 0b11000000) != 0b10000000) break;
    }
    return pos;
  };

  while (!test.eof()) {
    auto next = test.getNextToken();
    if (!next) {
      cout << "Parse error at: "
           << test.rest.substr(0, cutoff(test.rest, 20))
           << "...: no prefix matches known patterns "
              "(most probably due to unsupported ASCII character combinations. "
              "Is file encoded in UTF-8 and your syntax correct?)" << endl;
      test.ignoreNextCodepoint();
    } else cout << TestLexer::printToken(next.value()) << endl;
  }

  /*
  // See: https://en.cppreference.com/w/cpp/locale/wstring_convert/converted
  // The UTF-8 - UTF-32 standard conversion facet
  std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> cvt;

  // UTF-8 to UTF-32
  std::u32string utf32 = cvt.from_bytes(s);
  cout << "New UTF-32 string size: " << utf32.size() << '\n';
  cout << "converted() == " << cvt.converted() << '\n';

  // UTF-32 to UTF-8
  std::string utf8 = cvt.to_bytes(utf32);
  cout << "New UTF-8 string size: " << utf8.size() << '\n';
  cout << "converted() == " << cvt.converted() << '\n';

  cout << utf8 << endl;
  */

  return 0;
}
