using Documenter
push!(LOAD_PATH,"../src/")

using BooleanSatisfiability

makedocs(sitename="BooleanSatisfiability.jl",
repo = "https://github.com/elsoroka/BooleanSatisfiability.jl",
clean=true,
draft=true,
root=".",
source  = "src",
modules = [BooleanSatisfiability],
pages = [
        "index.md",
        "tutorial.md",
        "faq.md",
        "Examples" => [
            "example_scheduling.md",
            "example_job_shop.md"
        ],
        "Library" => [
        "functions.md"
        ],
    ]
)