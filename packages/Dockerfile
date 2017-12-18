FROM fedora:27

LABEL maintainer="dnsampaio@gmail.com"

RUN dnf update -y && dnf install git-core ginac-devel glpk-devel gcc-c++ qepcad-B -y &&  dnf clean all && rm -rf /var/cache/dnf

RUN git clone https://gitlab.inria.fr/nunessam/pghc.git 
RUN cd pghc/FM/ && make -j4 && cd /pghc/converters/simplifier2iscc/ && make && cd /pghc/converters/simplifier2reduce/ && make
