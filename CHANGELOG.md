# Change Log

### 2.1.0
Major: 
- Create a (still in development and improvement) benchmarking system. A guide on how to use it is in the README.
- Conduct an experiment on the performance of different LLMs, using the developed infrastructure. Benchmarking report is located in the [docs folder](etc/docs/benchmarking_report.md).
- Correctly handle and display settings which occur when the user settings are not correctly set.

Minor: 
- Set order of contributed settings.
- Add a comprehensive user settings guide to the README. 
- Fix issue with Grazie service not being able to correctly accept coq ligatures.
- Fix issue that occured when generated proof contained `Proof using {...}.` construct. 

### 2.0.0
- Added multiple strategies for ranking theorems from the working file. As LLM context window is limited, we sometimes should somehow choose a subset of theorems we want to provide as references to the LLM. Thus, we have made a few strategies for ranking theorems. Now there are only 2 of them, but there are more to come. Now we have a strategy that randomly picks theorems, and also the one that ranks them depending on the distance from the hole.
- Now different holes are solved in parallel. This is a huge improvement in terms of performance.
- Implemented multi-round fixing procedure for the proofs from the LLM. It can now be configured in the settings. One can set the amount of attempts for the consequtive proof fixing with compiler feedback. 
- Added an opportunity to use LM Studio as a language model provider.
- More accurate token count. Tiktoken is now used for open-ai models.
- Different logging levels now supported. 
- The LLM iterator now supports adding a sequence of models for each service. This brings freedom to the user to experiment with different model parameters.
- Now temperature, prompt, and other parameters are configurable in the settings.

### 1.9.0 
- Huge refactoring done. Project re organized.

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