FROM julia:1.9

RUN apt-get update  && apt-get install -y git
RUN git clone https://github.com/elsoroka/Satisfiability.jl.git
RUN apt-get install -y z3

WORKDIR /Satisfiability.jl
RUN chmod +x examples/paper_examples/run_examples.sh
RUN git checkout dev
CMD julia test/runtests.jl
