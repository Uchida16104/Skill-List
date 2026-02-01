# Linux Installation Guide

Setup instructions for Debian, Ubuntu, CentOS, and other Linux distributions.

## For Debian/Ubuntu

### Step 1: Update System
```bash
sudo apt update && sudo apt upgrade -y
```

### Step 2: Install Build Essentials
```bash
sudo apt install -y build-essential curl wget git pkg-config libssl-dev
```

### Step 3: Install Node.js
```bash
curl -fsSL https://deb.nodesource.com/setup_18.x | sudo -E bash -
sudo apt install -y nodejs
```

### Step 4: Install Rust
```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source "$HOME/.cargo/env"
```

### Step 5: Install .NET and Dafny
```bash
wget https://dot.net/v1/dotnet-install.sh
chmod +x dotnet-install.sh
./dotnet-install.sh --channel 7.0
export PATH="$PATH:$HOME/.dotnet"
dotnet tool install --global dafny
```

### Step 6: Install F*
```bash
sudo apt install -y opam
opam init -y
eval $(opam env)
opam install fstar
```

### Step 7: Clone and Build
```bash
git clone https://github.com/Uchida16104/Skill-List.git
cd Skill-List
git checkout -b skill-list
chmod +x scripts/*.sh
./scripts/compile_all.sh
```

### Step 8: Run Application
```bash
# Terminal 1 - Backend
cd backend
cargo run --release

# Terminal 2 - Frontend
cd frontend
npm install
npm run dev
```

## For CentOS/RHEL

### Install Dependencies
```bash
sudo yum groupinstall -y "Development Tools"
sudo yum install -y openssl-devel
```

Follow similar steps as Debian but use `yum` instead of `apt`.

## For Android (Termux)

```bash
pkg install nodejs-lts rust git
# Follow remaining steps similar to Debian
```

## Troubleshooting

- **Permission Denied**: Use `chmod +x` on scripts
- **Port in Use**: Change PORT environment variable
- **Build Errors**: Ensure all dependencies are installed

Open browser to http://localhost:3000
