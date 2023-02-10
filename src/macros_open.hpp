// "Syntax enhancements".
#define required = 0

// Used for declaring a class as "interface".
// See: https://softwareengineering.stackexchange.com/questions/235674/what-is-the-pattern-for-a-safe-interface-in-c
#define interface(T)                                 \
protected:                                           \
  T() noexcept = default;                            \
  T(T const&) noexcept = default;                    \
  T(T&&) noexcept = default;                         \
  auto operator=(T const&) noexcept -> T& = default; \
  auto operator=(T&&) noexcept -> T& = default;      \
public:                                              \
  virtual ~T() = default

#define unreachable   unreachable(__FILE__, __LINE__, static_cast<char const*>(__func__))
#define unimplemented unimplemented(__FILE__, __LINE__, static_cast<char const*>(__func__))
#define assert(expr)  assert(!!(expr), #expr, __FILE__, __LINE__, static_cast<char const*>(__func__))
