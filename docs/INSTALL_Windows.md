# Windows Installation Guide

Complete setup instructions for building the Skill List project on Windows 10/11.

## Prerequisites

- Windows 10 or Windows 11 (64-bit)
- At least 8GB RAM
- 10GB free disk space
- Administrator access

## Step 1: Install Windows Terminal (Optional but Recommended)

Download from Microsoft Store or:
```powershell
winget install Microsoft.WindowsTerminal
```

## Step 2: Install Node.js

Download Node.js 18 LTS from https://nodejs.org/

Run the installer with default settings. Verify:
```powershell
node --version
npm --version
```

## Step 3: Install Rust

Download and run rustup-init.exe from https://rustup.rs/

Accept defaults and restart your terminal. Verify:
```powershell
rustc --version
cargo --version
```

## Step 4: Install .NET SDK and Dafny

Download .NET 7.0 SDK from https://dotnet.microsoft.com/download

Install Dafny:
```powershell
dotnet tool install --global dafny
```

Add to PATH: `C:\Users\<YourUsername>\.dotnet\tools`

## Step 5: Install F*

Download prebuilt F* from https://github.com/FStarLang/FStar/releases

Extract to `C:\Program Files\FStar`
Add `C:\Program Files\FStar\bin` to PATH

## Step 6: Install Git

Download from https://git-scm.com/download/win

Use Git Bash for Unix-like commands.

## Step 7: Clone Repository

```bash
git clone https://github.com/Uchida16104/Skill-List.git
cd Skill-List
git checkout -b skill-list
```

## Step 8: Build and Run

In Git Bash or PowerShell:

```bash
./scripts/compile_all.sh  # May need WSL or Git Bash
cd backend
cargo build --release
cargo run

# New terminal
cd frontend
npm install
npm run dev
```

## Troubleshooting

- **Visual Studio Build Tools**: If Rust compilation fails, install VS Build Tools
- **OpenSSL**: Install from https://slproweb.com/products/Win32OpenSSL.html
- **Path Issues**: Ensure all tools are in System PATH

Visit http://localhost:3000 to see the application.
