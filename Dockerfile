FROM ubuntu:20.04

ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=Asia/Shanghai

RUN ln -fs /usr/share/zoneinfo/$TZ /etc/localtime && \
    echo "$TZ" > /etc/timezone && \
    apt-get update && \
    apt-get install -y tzdata

RUN apt-get update && \
    apt-get install -y \
        software-properties-common \
        build-essential \
        gcc \
        llvm-10 \
        cmake \
        flex \
        bison \
        libgmp-dev \
        ppl-dev \
        libgmp10 \
        libclang-dev \
        curl \
        time

RUN add-apt-repository ppa:deadsnakes/ppa -y && \
    apt-get update && \
    apt-get install -y python3.10 python3.10-dev python3.10-distutils python3.10-venv && \
    ln -s /usr/bin/python3.10 /usr/bin/python
    
RUN curl https://bootstrap.pypa.io/get-pip.py -o get-pip.py && \
    python3.10 get-pip.py && \
    pip install \
        pyyaml \
        tqdm

RUN useradd -ms /bin/bash vmcai
WORKDIR /home/vmcai
USER vmcai
COPY --chown=vmcai:vmcai . /home/vmcai/
