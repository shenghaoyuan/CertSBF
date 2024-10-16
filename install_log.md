# VirtualBox + Ubuntu 22.04
```shell
sudo apt update
sudo apt upgrade -y
sudo apt install build-essential curl wget git vim openjdk-11-jdk unzip -y

wget https://isabelle.in.tum.de/dist/Isabelle2024_linux.tar.gz
tar -xzf Isabelle2024_linux.tar.gz
echo 'export PATH="$HOME/Isabelle2024/bin:$PATH"' >> ~/.bashrc
vim .bashrc
source ~/.bashrc
isabelle version
wget https://www.isa-afp.org/release/afp-current.tar.gz
tar -xzf afp-current.tar.gz
cd /YOUR-PATH/afp/thys
isabelle components -u .

# go to our repo
cd THIS-REPO

sudo apt install opam
opam switch create sbpf ocaml-base-compiler.4.14.1
eval $(opam env --switch=sbpf)
opam install ocamlfind yojson

curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
#export PATH="$HOME/.cargo/bin:$PATH"
```