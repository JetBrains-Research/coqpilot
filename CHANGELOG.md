# Change Log


### 1.2.0
- Fix error with llm silently failing. Now everything that comes from llm that is not handled inside plugin is presented to user as a message (i.e. incorrect apiKey exception). 
- Fix toggle button.
- Fix diagnostics being shown to non coq-lsp plugin coq users. 
- Add output stream for the logs in vscode output panel.

### 1.1.0

Now proof generation could be run in any position inside the theorem. There is no need to retake file snapshot after each significant file change. 
More communication with `coq-lsp` is added. Saperate package `coqlsp-client` no longer used.

### 0.0.1

Initial release of coqpilot. 