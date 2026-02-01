# macOS Installation Guide

This guide provides step-by-step instructions for building and running the Skill List project on macOS.

## Prerequisites

Before beginning, ensure your macOS system meets the following requirements:

- macOS 11 (Big Sur) or later
- At least 8GB of RAM
- 5GB of free disk space
- Administrator access for installing tools

## Step 1: Install Homebrew

Homebrew is the package manager for macOS that will help install most required tools.

Open Terminal and run:

```bash
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
```

After installation, add Homebrew to your PATH (for Apple Silicon Macs):

```bash
echo 'eval "$(/opt/homebrew/bin/brew shellenv)"' >> ~/.zprofile
eval "$(/opt/homebrew/bin/brew shellenv)"
```

For Intel Macs, Homebrew installs to `/usr/local` and is automatically in your PATH.

## Step 2: Install Node.js and npm

Install Node.js version 18 or later:

```bash
brew install node
```

Verify the installation:

```bash
node --version  # Should show v18.x.x or later
npm --version   # Should show 9.x.x or later
```

## Step 3: Install Rust

Install Rust using rustup, the official Rust installer:

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

Follow the on-screen prompts and select the default installation option.

After installation, configure your current shell:

```bash
source "$HOME/.cargo/env"
```

Verify the installation:

```bash
rustc --version  # Should show 1.70.0 or later
cargo --version  # Should show 1.70.0 or later
```

## Step 4: Install Dafny

Dafny can be installed via the .NET SDK. First, install .NET:

```bash
brew install dotnet
```

Then install Dafny as a global tool:

```bash
dotnet tool install --global dafny
```

Add the .NET tools directory to your PATH in `~/.zprofile` or `~/.bash_profile`:

```bash
export PATH="$PATH:$HOME/.dotnet/tools"
```

Reload your shell configuration:

```bash
source ~/.zprofile  # or source ~/.bash_profile
```

Verify the installation:

```bash
dafny --version
```

## Step 5: Install F*

F* requires OCaml. Install OCaml and OPAM (OCaml package manager):

```bash
brew install opam
opam init -y
eval $(opam env)
```

Install F* via OPAM:

```bash
opam install fstar
```

Alternatively, you can download prebuilt F* binaries from the official repository:

```bash
cd ~/Downloads
curl -L https://github.com/FStarLang/FStar/releases/latest/download/fstar-Darwin-x86_64.tar.gz -o fstar.tar.gz
tar -xzf fstar.tar.gz
sudo mv fstar /usr/local/
export PATH="$PATH:/usr/local/fstar/bin"
```

Add F* to your PATH permanently by adding this line to `~/.zprofile`:

```bash
echo 'export PATH="$PATH:/usr/local/fstar/bin"' >> ~/.zprofile
```

Verify the installation:

```bash
fstar.exe --version
```

## Step 6: Install Git

Git should be pre-installed on macOS. Verify:

```bash
git --version
```

If not installed, install via Homebrew:

```bash
brew install git
```

Configure Git with your information:

```bash
git config --global user.name "Your Name"
git config --global user.email "your.email@example.com"
```

## Step 7: Clone the Repository

Clone the Skill List repository from GitHub:

```bash
cd ~
git clone https://github.com/Uchida16104/Skill-List.git
cd Skill-List
git checkout -b skill-list
```

If you want to work on an existing branch:

```bash
git checkout skill-list
```

## Step 8: Verify Toolchain

Run the toolchain verification script:

```bash
chmod +x ./scripts/check_toolchain.sh
./scripts/check_toolchain.sh
```

This script will verify that all required tools are properly installed.

## Step 9: Compile All Sources

Compile all F* and Dafny sources to their target languages:

```bash
chmod +x ./scripts/compile_all.sh
./scripts/compile_all.sh
```

This process may take several minutes. The script will:

1. Compile F* sources to JavaScript, CSS, Svelte, Tailwind, HTMX, Rust, and Python
2. Compile Dafny sources to JavaScript, CSS, Svelte, Tailwind, Alpine.js, HTMX, C#, Rust, Python, and database interfaces
3. Generate Mermaid diagrams for process flows
4. Prepare both frontend and backend for local development

## Step 10: Build and Run Backend

Navigate to the backend directory and build:

```bash
cd backend
cargo build --release
```

The first build will download and compile all dependencies, which may take 10-15 minutes.

Run the backend server:

```bash
cargo run --release
```

Or simply:

```bash
./target/release/skill-list-backend
```

The backend server will start on `http://0.0.0.0:10000`.

You should see output similar to:

```
[INFO] Starting Skill List Backend Server
[INFO] Listening on 0.0.0.0:10000
```

Test the backend by opening a new terminal window and running:

```bash
curl http://localhost:10000/health
```

Expected response:

```json
{"status":"healthy","service":"skill-list-backend","version":"0.1.0"}
```

## Step 11: Build and Run Frontend

Open a new terminal window and navigate to the frontend directory:

```bash
cd ~/Skill-List/frontend
```

Install dependencies:

```bash
npm install
```

Create a `.env.local` file for local development:

```bash
echo "NEXT_PUBLIC_API_URL=http://localhost:10000" > .env.local
```

Run the development server:

```bash
npm run dev
```

The frontend will start on `http://localhost:3000`.

Open your web browser and navigate to `http://localhost:3000`. You should see the Skill List application with sample data loaded from the backend.

## Step 12: Run Verification Tests

In a new terminal window, run the verification test suite:

```bash
cd ~/Skill-List
chmod +x ./scripts/verify_spec.sh
./scripts/verify_spec.sh
```

This will verify all F* and Dafny specifications and ensure formal correctness.

## Development Workflow

For active development, keep both servers running in separate terminal windows:

**Terminal 1 - Backend:**
```bash
cd ~/Skill-List/backend
cargo watch -x run  # Auto-recompiles on file changes (install with: cargo install cargo-watch)
```

**Terminal 2 - Frontend:**
```bash
cd ~/Skill-List/frontend
npm run dev  # Auto-reloads on file changes
```

## Building for Production

Build optimized production versions:

**Backend:**
```bash
cd backend
cargo build --release
```

**Frontend:**
```bash
cd frontend
npm run build
npm start  # Runs production build
```

## Troubleshooting

### F* or Dafny Not Found

If F* or Dafny commands are not recognized, ensure they are in your PATH:

```bash
echo $PATH
```

Add them to your `~/.zprofile`:

```bash
export PATH="$PATH:/usr/local/fstar/bin:$HOME/.dotnet/tools"
```

Then reload:

```bash
source ~/.zprofile
```

### Rust Compilation Errors

If you encounter Rust compilation errors, try updating Rust:

```bash
rustup update
```

### npm Install Failures

If npm install fails, try clearing the cache:

```bash
npm cache clean --force
rm -rf node_modules package-lock.json
npm install
```

### Port Already in Use

If port 10000 or 3000 is already in use, you can change the ports:

**Backend:** Set the PORT environment variable:
```bash
PORT=8080 cargo run
```

**Frontend:** Next.js will automatically try the next available port (3001, 3002, etc.)

### OpenSSL Errors on Apple Silicon

If you encounter OpenSSL-related errors on M1/M2 Macs:

```bash
brew install openssl
export OPENSSL_DIR=$(brew --prefix openssl)
export PKG_CONFIG_PATH="${OPENSSL_DIR}/lib/pkgconfig"
```

## Updating Dependencies

Keep your development environment up to date:

```bash
# Update Homebrew packages
brew update && brew upgrade

# Update Rust
rustup update

# Update Node packages
cd frontend
npm update

# Update Rust dependencies
cd ../backend
cargo update
```

## Next Steps

Once your local environment is running successfully:

1. Review the generated artifacts in `frontend/frontend/` and `backend/backend/`
2. Explore the F* and Dafny source files in `verification/`
3. Make modifications and see them reflected in real-time
4. Run verification tests to ensure formal correctness is maintained
5. Follow the deployment guide in `docs/DEPLOYMENT.md` to deploy to Render and Vercel

## Additional Resources

- F* Documentation: https://www.fstar-lang.org/tutorial/
- Dafny Documentation: https://dafny.org/dafny/
- Rust Documentation: https://doc.rust-lang.org/
- Next.js Documentation: https://nextjs.org/docs

## Support

If you encounter issues not covered in this guide, please:

1. Check the troubleshooting section above
2. Review logs in terminal output
3. Open an issue on the GitHub repository
4. Consult the official documentation for each tool

You are now ready to develop and verify your Skill List application on macOS!
