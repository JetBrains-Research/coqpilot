# Changelog

## 2.4.2

- Fix premise selection bug in benchmarks: in `v2.4.1`, a theorem for which the completion was issued was accidentally added to the list of premises. This was fixed in this release.
We encountered difficulty setting the correct `coq-lsp` path in the settings, both for the `coq-lsp` plugin itself and for `coqpilot`. When using the `nix` environment, it is common for the path to be updated by hand, and it is not always done correctly. Therefore, we added a warning message to the user, which is shown when `coqpilot` suspects that the build of `coq-lsp` on the given path is not the expected one.

## 2.4.1

Hot fix with update of dependencies to fix the issue on extension activation.

## 2.4.0

The version increment is minor, yet the changes are significant. The main focus of this release was to improve interaction with the `coq-lsp` server. We now completely got rid of temporary files in the `extension` part of `CoqPilot`. This was done thanks to [ejgallego](https://github.com/ejgallego) and his improvements in `coq-lsp`. Now checking of proofs is done via the `proof/goals` request via `command` parameter, which is much more reliable and faster. Now a single `lsp` server is created for the plugin until being explicitly closed, and it tracks changes in the file. If you are using `coq-lsp` plugin itself, it will help you to always keep track of whether file is checked or not. When `CoqPilot` is ran on a completely checked file, it will not bring any significant overhead apart from requests to the Completion Services. 

### Public changes
- Added a toggle button to enable/disable the extension
- Using the toggle switch, user can now abort the proof generation process
- Significant performance improvements in proof checking that are especially easy to see for large files

### Internal changes
- Get rid of temporary files in the `extension` part of `CoqPilot`
- Refactor `CoqLspClient` 
- Make computation of `initialGoal` for premises optional to avoid unnecessary requests to `coq-lsp`
- Introduce `with-coq-lsp` wrappers to encapsulate correct `CoqLspClient` disposal
- Introduce `CoqLspClient.withTextDocument(...)` wrapper to encapsulate opening and closing a document with `coq-lsp`

## 2.3.0

**A major upgrade of the benchmarking system**: At the moment, only a little **new** functionality is provided; moreover, the ability to run benchmarks on Tactician/CoqHammer is temporarily unavailable. However, it will soon be restored and improved. Excessive work has been done to make the benchmarking system more flexible, secure, robust, self-contained, and easy to use. Experiments via our benchmarking framework have been made more accessible than ever. The configurability and reliability of the pipeline have been improved drastically. In a nutshell, the main features of the improved benchmarking system include:
- Flexible DSL for input setup
- Extensive configuration for fine-grained experiments
- Support for single and multi-workspace runs
- Dataset caching
- Comprehensive logging
- Fail-fast strategy
- Additional metrics (tokens used, context theorems, proof generation stats)

An extensive benchmarking guide is now available in [BENCHMARKING_FRAMEWORK_GUIDE.md](etc/docs/benchmark/BENCHMARKING_FRAMEWORK_GUIDE.md).

We are looking forward to your feedback and suggestions for further improvements/new features.

## 2.2.7

### Internal changes: 
- Allow prod/stgn auth-type for JetBrains AI service.

## 2.2.6

### Public changes

- Allow manually modifying the location of the `coq-lsp` executable in the settings. This is useful when the `coq-lsp` executable is not in the PATH. Alongside, correctly handle the case when the `coq-lsp` executable is not found.
- Improve proof extraction from the LLM services for proofs, containing `Proof using X Y Z.` and similar constructs. Improve the handling of the obfuscatedly generated proofs by small language models, such as `LLaMA` through `LMStudio`.
- Add a hotkey for solving admits inside selection: `ctrl+shift+[BracketRight]` on Windows and Linux, `shift+cmd+[BracketRight]` on MacOS.

### Internal changes
- Update private headers, sent to JetBrains-AI services, to identify the client as CoqPilot.

## 2.2.5

- Contribute the new benchmarking report for 300 theorems. 
- Update the README with clarifications regarding Nix/Opam for benchmarking 
- Update the benchmarking framework to allow using external services
- Allow configuring timeouts, specific theorems to check and other parameters for benchmarking

## 2.2.4

Contains no public changes. Updates the endpoints for the Grazie LLM Service in order to make it work with the latest version of Grazie service tokens. 

## 2.2.3

- Fix critical issue with proof checking. Before, when the choices parameter was high, sometimes the wrong proof could be generated and not identified as incorrect. 
- Updated CI with a build for MacOS. 
- Deploy the README to gh-pages from CI using jekyll.
- Fix and extend README, benchmarking report.

## 2.2.2

- Fix and refactor CI. Publishing a new release is now a manual process.

## 2.2.1

- Fix a bug where the `tmp` package was not being installed in the release version.

## 2.2.0

### Public changes

- Support time estimation for LLM services to become available after failure via logging proof-generation requests. This information is shown to the user. 
- Set up interaction between `LLMService`-s and UI to report errors that happened during proof-generation.
- Improve LLM services' parameters: their naming, transparency, and description.
    - Introduce `modelId` to distinguish a model identifier from the name of an OpenAI / Grazie model.
    - Rename `newMessageMaxTokens` to `maxTokensToGenerate` for greater clarity.
    - Update the settings description, and make it more user-friendly.
- Significantly improve settings validation.
    - Use parameters resolver framework to resolve parameters (with overrides and defaults) and validate them.
    - Support messages about parameter resolution: both failures and unexpected overrides.
    - Clarify existing error messages.
    - Add some general checks: input models have unique `modelId`-s, there are models to generate proofs with.
- Improve interaction with OpenAI.
    - Notify the user of configuration errors (invalid model name, incorrect API key, maximum context length exceeded) and connection errors.
    - Support resolution of `tokensLimit` and `maxTokensToGenerate` with recommended defaults for known models.
- Fix minor bugs and make minor improvements detected by thorough testing.

### Internal changes

- Rework and document LLMService architecture: `LLMServiceInternal`, better facades, powerful typing.
- Introduce hierarchy for LLMService errors. Support proper logging and error handling inside `LLMService`-s.
- Rework settings validation.
    - Refactor `SettingsValidationError`, move all input parameters validation to one place and make it coherent.
    - Design and implement a powerful and well-documented parameters resolver framework.

### Testing infrastructure changes

- Test the LLM Services module thoroughly. 
- Improve test infrastructure in general by introducing and structuring utils.
- Fix the issue with building test resources on CI. 
- Set up CI debugging, and enable launching CI manually. 
  Double the speed of CI by setting caches.

## 2.1.0

Major: 
- Create a (still in development and improvement) benchmarking system. A guide on how to use it is in the README.
- Conduct an experiment on the performance of different LLMs, using the developed infrastructure. The benchmarking report is located in the [docs folder](etc/docs/benchmarking_report01.md).

Minor: 
- Set the order of contributed settings.
- Add a comprehensive user settings guide to the README. 
- Fix the issue with Grazie service not being able to correctly accept coq ligatures.
- Fix the issue that occurred when the generated proof contained the `Proof using {...}.` construct. 

## 2.0.0

- Added multiple strategies for ranking theorems from the working file. As the LLM context window is limited, we sometimes should somehow choose a subset of theorems we want to provide as references to the LLM. Thus, we have made a few strategies for ranking theorems. Now there are only 2 of them, but there are more to come. Now we have a strategy that randomly picks theorems, and also the one that ranks them depending on the distance from the hole.
- Now different holes are solved in parallel. This is a huge improvement in terms of performance.
- Implemented multi-round fixing procedure for the proofs from the LLM. It can now be configured in the settings. One can set the number of attempts for the consecutive proof fixing with compiler feedback. 
- Added an opportunity to use LM Studio as a language model provider.
- More accurate token count. Tiktoken is now used for OpenAI models.
- Different logging levels are now supported. 
- The LLM iterator now supports adding a sequence of models for each service. This brings freedom to the user to experiment with different model parameters.
- Now temperature, prompt, and other parameters are configurable in the settings.

## 1.9.0

- Huge refactoring is done. Project reorganized.

## 1.5.3

- Fix Grazie service request headers and endpoint. 

## 1.5.2

- Fix issue with double document symbol provider registration (@Alizter, [#9](https://github.com/JetBrains-Research/coqpilot/issues/9))

## 1.5.1

- Add support for the Grazie platform as an LLM provider.  

## 1.5.0

- Now when the hole can be solved by a single tactic solver, using predefined tactics, OpenAI and Grazie will not be called, LLMs are now fetched consequently. 
- Parallel hole completion is unfortunately postponed due to the implementation complexity. Yet, hopefully, will still be implemented in milestone `2.0.0`.

## 1.4.6

- Fix the issue with the plugin breaking after parsing a file containing theorem without the `Proof.` keyword.

## 1.4.5

- Fix formatting issues when inserting the proof into the editor.

## 1.4.4

- Do not require a theorem to be `Admitted.` for CoqPilot to prove holes in it.
- Correctly parse theorems that are declared with the `Definition` keyword.

## 1.4.3

- Tiny patch with the shuffling of the hole array.

## 1.4.2

- Now no need to add a dot at the end of the tactic, when configuring a single tactic solver.
- Automatic reload settings on change in the settings file. Not all settings are reloaded automatically, 
but most ones are. The ones that are not automatically reloaded: `useGpt`, `coqLspPath`, `parseFileOnInit`.
- Added a command that solves admits in a selected region. Also added that command to the context menu (right-click in the editor).
- Fix toggle extension. 

## 1.4.1

- Add a possibility to configure a single tactic solver.

## 1.4.0

- Add a command to solve all admitted holes in the file.
- Fixing bugs with coq-lsp behavior. 

## 1.3.1

- Test coverage increased.
- Refactoring client and ProofView.  
- Set up CI. 

## 1.3.0

- Fix bug while parsing regarding the updated Fleche doc structure in coq-lsp 0.1.7.
- When GPT generated a response containing three consecutive backtick symbols it tended to 
break the typecheking of the proof. Now solved. 
- Speed up the file parsing process. 

## 1.2.1

- Add clearing of aux file after parsing. 

## 1.2.0

- Fix error with llm silently failing. Now everything that comes from LLM that is not handled inside the plugin is presented to the user as a message (i.e. incorrect apiKey exception). 
- Fix the toggle button.
- Fix diagnostics being shown to non-`coq-lsp` plugin coq users. 
- Add output stream for the logs in the vscode output panel.

## 1.1.0

Now proof generation could be run in any position inside the theorem. There is no need to retake a file snapshot after each significant file change. 
More communication with `coq-lsp` is added. The separate package `coqlsp-client` is no longer used.

## 0.0.1

The initial release of CoqPilot. 