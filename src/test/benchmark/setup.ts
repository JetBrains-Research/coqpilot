import { LLMServiceIdentifier } from "./framework/structures/llmServiceIdentifier";

const experiment = new Experiment();

ExclusionBundle
    .withLLMServices(LLMServiceIdentifier.OPENAI)
    .withMatchingModelParams(
        (modelParams) => modelParams.multiroundProfile.maxRoundsNumber > 1
    )
    // .withTargetsFromFile("file.txt", "mixed_theorem")
    // .withAllTargetsFromFile("file.txt")
    .excludeFrom(experiment);


BenchmarkingBundle.withLLMService(LLMServiceIdentifier.GRAZIE)
    // .withModelsParamsCommons({ranker: ..., apiKey: ..., tokensLimit: ...})
    .withModelsParams(
        {
            modelId: "grazie",
            modelName: "openai-gpt-4",
            apiKey: "hehe",
            choices: 15,
            newMessageMaxTokens: 1000,
            tokensLimit: 2000,
            multiroundProfile: {
                maxRoundsNumber: 1,
            },
        },
        {
            modelId: "grazie",
            modelName: "openai-gpt-4",
            apiKey: "hehe",
            choices: 15,
            newMessageMaxTokens: 1000,
            tokensLimit: 2000,
            multiroundProfile: {
                maxRoundsNumber: 1,
            },
        }
    )
    // withTargetsFromFile("file.txt", "mixed_theorem")
    // withTargetsFromFile("file.txt")
    // withTargetsFromDirectory("data")
    .withTargets(
        {
            name: "Complete mixed examples (both simple & hard) with `auto`",
            items: [new DatasetItem("mixed_benchmark.v")],
        },
        {
            name: "Complete mixed examples (both simple & hard) with `auto`",
            items: [new DatasetItem("mixed_benchmark.v")],
        }
    )
    .appendTo(experiment);

const result = experiment.run(); // + params in run
console.log(result);
