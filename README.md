# CertSBF

# How to install
- Isabelle/HOL 2023 (please set your PATH with e.g. `/home/shyuan/GitLab/Isabelle2023`)
- seL4 project: L4V (Follow [SetUp](https://github.com/seL4/l4v/blob/master/docs/setup.md), please remember change all l4v prefix `/home/shyuan/GitHub/l4v/` to your l4v path)

ps: some sel4-install soft requires a magic tool(V-P-N):
- `repo`: can only [install repo manually](https://gerrit.googlesource.com/git-repo/+/HEAD/README.md)
```shell
$ mkdir -p ~/.bin
$ PATH="${HOME}/.bin:${PATH}"
$ curl https://storage.googleapis.com/git-repo-downloads/repo > ~/.bin/repo
$ chmod a+rx ~/.bin/repo
```
NB: please set your PATH with e.g. `/home/shyuan/.bin`
- `cabal-install`
```shell
stack install cabal-install
```
- `repo init`
```shell
repo init -u https://git@github.com/seL4/verification-manifest.git
repo sync
```
- `l4v`
```shell
./isabelle/bin/isabelle components -a
```
