The following artifact evaluation reproduces Table 1 

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
And then build according to the instructions. This will take ~2 hours, depending on your system.

Now, after everything is installed and built, you can 
