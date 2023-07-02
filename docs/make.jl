using Documenter
push!(LOAD_PATH,"../src/")

using BooleanSatisfiability

fmt = Documenter.Writers.HTMLWriter.HTML(edit_link="main")

makedocs(sitename="BooleanSatisfiability.jl",
repo = "https://github.com/elsoroka/BooleanSatisfiability.jl/blob/{commit}{path}#L{line}",
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
    ],
format=fmt,
)

Documenter.deploydocs(
    repo = "github.com/elsoroka/BooleanSatisfiability.jl.git",
    devbranch = "main",
    push_preview = true,
)