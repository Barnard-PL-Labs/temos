apt update
apt install python3 python3-pip git curl
python3 -m pip install --upgrade pip
python3 -m pip install pandas
git clone https://github.com/Barnard-PL-Labs/temos 
cd temos
git fetch origin art-eval-pldi22
curl --proto '=https' --tlsv1.2 https://sh.rustup.rs -sSf | sh
source $HOME/.cargo/env
