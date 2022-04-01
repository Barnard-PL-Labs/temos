sed -i -re 's/([a-z]{2}\.)?archive.ubuntu.com|security.ubuntu.com/old-releases.ubuntu.com/g' /etc/apt/sources.list
apt update
apt install python3-pip
python3 -m pip install --upgrade pip
python3 -m pip install pandas colorama
curl --proto '=https' --tlsv1.2 https://sh.rustup.rs -sSf | sh
source $HOME/.cargo/env
git clone https://github.com/wonhyukchoi/tsltools.git tsltools && cd tsltools && make
mv cfm2code ../bin/
mv tsl2tlsf ../bin/
cd ..
chmod +x bin/tsl2js.sh
chmod +x bin/cvc4
cargo build --release
