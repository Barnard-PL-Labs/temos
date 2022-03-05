** Setup and running the evaluation **

The following artifact evaluation reproduces the experimental evaluation portion of Table 1.

It uses the tool TeMoS (Temporal Stream Logic Modulo Theories Synthesis).

First, to get started, please download the Docker image that already contains multiple dependencies installed, available either through the zenodo link, or if you have Docker installed, pullable through Docker Hub:
`docker pull wonhyukchoi/tsl-strix-docker`

Afterwards, enter the docker image, e.g. by
`docker run -it wonhyukchoi/tsl-strix-docker /bin/bash`

You will now need to clone the directory.
`git clone --single-branch --branch art-eval-pldi22 https://github.com/Barnard-PL-Labs/temos.git`
`cd temos`

Then, give permission to the setup script:
`chmod +x setup.sh`

Run the setup script:
`./setup.sh`

NOTE: we have also included a binary version of CVC4. However, if you wish to build from source instead, you can clone 
`git clone https://github.com/cvc5/cvc5`
`git checkout 34798fb86eabe7b9aaff86be23a7a3428ebfc957`
And then build according to the instructions. This will take about two hours, depending on your system.


** Results of evaluation **

Now, after everything is installed and built, you can run the evaluation by
`python3 utils/eval_all.py`
which will present the running times of the various benchmarks as described in the paper.

The experimental evaluation in the paper focuses on the SyGuS and reactive synthesis times taken for each TSL Modulo Theories specification.
Since runtime will vary depending on each system and its load, to check that the artficat is consisten with the paper, we suggest that the reviewers check the primary claim of the paper: SyGuS synthesis times are generally much smaller than the reactive synthesis times.

For the number of assumptions, since we rely on CVC4 to make synthesis decisions for us, this may result in a non-deterministic number of assumptions generated.
