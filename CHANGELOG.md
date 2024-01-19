# Change Log

### 1.5.3
- Fix Grazie service request headers and endpoint. 

### 1.5.2
- Fix issue with double document symbol provider registration (@Alizter, [#9](https://github.com/JetBrains-Research/coqpilot/issues/9))

### 1.5.1
- Add support of the Grazie platform as an llm provider.  

### 1.5.0
- Now when the hole can be solved by a single tactic solver, using predefined tactics, gpt will not be called, LLMs are now fetched consequently. 
- Parallel hole completion is unfortunately postponed due to the implementation complexity. Yet, hopefully, will still be implemented in milestone `2.0.0`.

### 1.4.6
- Fix issue with plugin breaking after parsing a file containing theorem without `Proof.` keyword.

### 1.4.5
- Fix formatting issues when inserting the proof into the editor.

### 1.4.4
- Do not require a theorem to be `Admitted.` for coqpilot to prove holes in it.
- Correctly parse theorems that are declared with `Definition` keyword.

### 1.4.3
- Tiny patch with shuffling of the hole array.

### 1.4.2
- Now no need to add dot in the end of the tactic, when configuring a single tactic solver.
- Automatic reload settings on change in the settings file. Not all settings are reloaded automatically, 
but the most ones are. The ones that are not automatically reloaded: `useGpt`, `coqLspPath`, `parseFileOnInit`.
- Added command that solves admits in selected region. Also added that command to the context menu (right click in the editor).
- Fix toggle extension. 

### 1.4.1
- Add a possibility to configure a single tactic solver.

### 1.4.0
- Add command to solve all admitted holes in the file.
- Fixing bugs with coq-lsp behavior. 

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