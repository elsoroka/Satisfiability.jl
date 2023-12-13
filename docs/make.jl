# CALL THIS FILE FROM ../ (call `julia docs/make.jl`)
using Documenter
push!(LOAD_PATH, "$(pwd())/src/")

using Satisfiability

fmt = Documenter.Writers.HTMLWriter.HTML(edit_link="main")

makedocs(sitename="Satisfiability.jl",
#repo = Documenter.Remotes.GitHub("elsoroka", "Satisfiability.jl"),
clean=true,
draft=false,
checkdocs=:none,
source  = "src",
workdir=pwd(),
modules = [Satisfiability],
pages = [
        "index.md",
        "installation.md",
        "Tutorial" => [
        "tutorial.md",
        "interactive.md",
        "example_uninterpreted_func.md",
        "advanced.md",
        ],
        "faq.md",
        "Examples" => [
            "example_scheduling.md",
            "example_job_shop.md",
            "example_bv_lcg.md",
            "example_graph_coloring.md",
            "example_bad_assertions.md",
        ],
        "Library" => [
        "functions.md"
        ]
    ],
format=fmt,
)

Documenter.deploydocs(
    repo = "github.com/elsoroka/Satisfiability.jl.git",
    devbranch = "main",
    push_preview = true,
)