FROM julia:1.9

RUN apt-get update  && apt-get install -y git
RUN git clone https://github.com/elsoroka/Satisfiability.jl.git
RUN apt-get install -y z3

WORKDIR /Satisfiability.jl/examples/paper_examples
RUN chmod +x run_examples.sh
CMD julia test/runtests.jl
