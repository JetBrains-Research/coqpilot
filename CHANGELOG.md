# Changelog

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
