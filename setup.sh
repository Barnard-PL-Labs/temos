apt update
apt install python3 python3-pip git curl wget
python3 -m pip install --upgrade pip
python3 -m pip install pandas
git clone https://github.com/Barnard-PL-Labs/temos 
cd temos
git fetch origin art-eval-pldi22
git checkout art-eval-pldi22
curl --proto '=https' --tlsv1.2 https://sh.rustup.rs -sSf | sh
source $HOME/.cargo/env
# wget https://github.com/meyerphi/strix/releases/download/21.0.0/strix-21.0.0-1-x86_64-linux.tar.gz
# tar -xzvf strix-21.0.0-1-x86_64-linux.tar.gz
# mv strix bin
cargo build --release
chmod +x bin/cvc4
chmod +x bin/tsl2js.sh
chmod +x bin/strix_tlsf.sh
curl -sSL https://get.haskellstack.org/ | sh
git clone https://github.com/reactive-systems/tsltools.git tsltools && cd tsltools && make
mv tsltools/cfm2code bin/
mv tsltools/tsl2tlsf bin/
git clone https://github.com/reactive-systems/syfco.git && cd syfco && make
