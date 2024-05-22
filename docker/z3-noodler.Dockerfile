# This dockerfile was created by Michal Hecko
# Eternal glory to him
FROM debian:latest
RUN apt-get update -y
RUN apt-get install -y git make cmake gcc g++ python3

RUN git clone https://github.com/VeriFIT/mata.git mata
WORKDIR mata
RUN make -j`nproc` release
RUN make install

WORKDIR /
RUN git clone 'https://github.com/VeriFIT/z3-noodler.git' /z3-noodler
RUN mkdir -p /z3-noodler/build
WORKDIR /z3-noodler/build
RUN cmake -DCMAKE_BUILD_TYPE=Release ..
RUN make -j`nproc`
ENTRYPOINT ["./z3", "smt.string_solver=\"noodler\""]
