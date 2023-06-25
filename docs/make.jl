using Documenter
push!(LOAD_PATH,"../src/")

using BooleanSatisfiability

makedocs(sitename="BooleanSatisfiability.jl",
repo = "https://github.com/elsoroka/BooleanSatisfiability.jl",
clean=true,
root=".",
source  = "src",
pages = [
        "index.md",
        "tutorial.md",
        "Examples" => [
            "example_scheduling.md"
        ],
        "functions.md"
    ]
)