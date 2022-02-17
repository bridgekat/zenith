// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as vscode from 'vscode';

import {
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	TransportKind
} from 'vscode-languageclient/node';

let client: LanguageClient;


// ===== TEMP CODE BEGIN =====

// This method is called when the extension is activated
// Refer to: https://github.com/microsoft/vscode-extension-samples/blob/main/lsp-sample/client/src/extension.ts
// Refer to: https://github.com/digama0/mm0/blob/master/vscode-mm0/src/extension.ts
export function activate(context: vscode.ExtensionContext) {

  // ===== Output something =====

  // Use the console to output diagnostic information (console.log) and errors (console.error)
  // This line of code will only be executed once when your extension is activated
  console.log('Congratulations, your extension "apimu" is now active!');

  // ===== Register commands =====

  // The command has been defined in the package.json file
  // Now provide the implementation of the command with registerCommand
  // The commandId parameter must match the command field in package.json
  let disposable = vscode.commands.registerCommand('apimu.helloWorld', () => {
    // The code you place here will be executed every time your command is executed
    // Display a message box to the user
    if (client) {
      client.sendRequest('test', { 'str': '吱吱吱🐀' }).then((val: unknown) => {
        if (typeof val === 'object' && val) {
          let key = 'echo' as keyof typeof val;
          vscode.window.showInformationMessage(val[key]);
        }
      }, () => {});
    }
  });

  let restartServer = vscode.commands.registerCommand('apimu.restartServer', () => {
    if (client) { client.stop().then(startServer, startServer); }
    else { startServer(); }
  });

  let shutdownServer = vscode.commands.registerCommand('apimu.shutdownServer', () => {
    if (client) {
      client.stop().then(
        () => { vscode.window.showInformationMessage('Server stopped'); },
        () => { vscode.window.showInformationMessage('Server stopped'); }
      );
    }
  });

  context.subscriptions.push(disposable, restartServer, shutdownServer);
}

function startServer() {
  // Server executable path
  let config = vscode.workspace.getConfiguration('apimu');
  let executablePath: string = config.get('executablePath') || "testserver";

  // If the extension is launched in debug mode then the debug server options are used
  // Otherwise the run options are used
  let serverOptions: ServerOptions = {
    run: { command: executablePath, args: ['server'] },
    debug: { command: executablePath, args: ['server', '--debug'] }
  };

  // Options to control the language client
  let clientOptions: LanguageClientOptions = {
    // Register the server for .mu documents
    documentSelector: [{ scheme: 'file', language: 'apimu' }]
  };

  // Create the language client and start the client.
  client = new LanguageClient(
    'apimu-lsp-test-client',
    'ApiMu Language Server Protocol Test Client',
    serverOptions,
    clientOptions
  );

  // Start the client. This will also launch the server.
  client.start();

  // Print status
  vscode.window.showInformationMessage('Attempted to start server.');
}

// This method is called when the extension is deactivated
export function deactivate() {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
