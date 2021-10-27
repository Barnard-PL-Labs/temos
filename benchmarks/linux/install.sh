#/usr/bin/env bash
# On Ubutnu 18.04.6 LTS

yes | sudo apt update
yes | sudo apt upgrade
yes | sudo apt install git openssh-server
git clone https://github.com/wonhyukchoi/linux.git && cd linux && git checkout v5.4
cp /boot/config-$(uname -r) .config
make oldconfig
make clean
make -j $(getconf _NPROCESSORS_ONLN) deb-pkg LOCALVERSION=-custom
