sed -i -re 's/([a-z]{2}\.)?archive.ubuntu.com|security.ubuntu.com/old-releases.ubuntu.com/g' /etc/apt/sources.list
apt install python3-pip
python3 -m pip install --upgrade pip
python3 -m pip install pandas
curl --proto '=https' --tlsv1.2 https://sh.rustup.rs -sSf | sh
source $HOME/.cargo/env
git fetch origin art-eval-pldi22
git checkout art-eval-pldi22
git clone https://github.com/reactive-systems/tsltools.git tsltools && cd tsltools && make
mv tsltools/cfm2code bin/
mv tsltools/tsl2tlsf bin/
chmod +x bin/*
cargo build --release
