# Change Log

### 1.3.1
- Test coverage increased.
- Refactoring client and ProofView.  
- Set up CI. 

### 1.3.0
- Fix bug while parsing regarding the updated Fleche doc structure in coq-lsp 0.1.7.
- When GPT generated a response containing three consecutive backtick symbols it tended to 
break the typecheking of the proof. Now solved. 
- Speed up the file parsing process. 

### 1.2.1
- Add clearing of aux file after parsing. 

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