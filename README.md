# Skill List - Formal Verification Portfolio Project

A production-ready full-stack application demonstrating formal verification using F* and Dafny, compiled to multiple targets including JavaScript, CSS, Rust, Python, C#, and various database interfaces.

## Project Overview

This project showcases end-to-end formal verification in a modern web application stack:

- **Frontend**: Next.js deployed on Vercel with formally verified components
- **Backend**: Rust server deployed on Render with verified business logic
- **Verification**: F* and Dafny source files compiled to multiple target languages
- **Persistence**: Browser-based storage (IndexedDB, PouchDB, LocalStorage, SQL.js)

## Architecture

### Frontend (Vercel - Next.js)
Formally verified UI components and logic compiled from F* and Dafny to JavaScript, CSS, Svelte, Tailwind utilities, Alpine.js components, and HTMX endpoints.

### Backend (Render - Rust)
Verified server-side processing including process management, network handling, data analysis, and database operations compiled from F* and Dafny to Rust, C#, and Python.

### Verification Workflow
1. Write specifications in F* and Dafny
2. Verify correctness with formal tools
3. Compile to target languages (Rust, JS, Python, C#, etc.)
4. Integrate compiled artifacts into frontend and backend

## Directory Structure

```
skill-list-project/
├── verification/          # F* and Dafny source files
│   ├── fstar/            # F* specifications
│   └── dafny/            # Dafny specifications
├── frontend/             # Next.js application
│   └── frontend/         # Compiled verification artifacts
│       ├── Dafny/        # Dafny → JS, CSS, Svelte, Tailwind, Alpine, HTMX
│       └── FStarLang/    # F* → JS, CSS, Svelte, Tailwind, HTMX
├── backend/              # Rust server
│   └── backend/          # Compiled verification artifacts
│       ├── process/      # Process management (Dafny/F* → Rust, C#)
│       ├── analysis/     # Data analysis (Dafny/F* → Python3)
│       ├── network/      # Network handling (Dafny/F* → Rust)
│       └── database/     # Storage interfaces (Dafny/F* → multiple targets)
├── scripts/              # Build and verification scripts
└── docs/                 # Platform-specific installation guides
```

## Quick Start

### Prerequisites
- Node.js 18+ and npm
- Rust 1.70+
- Dafny 4.0+
- F* (latest stable)
- Git

### Local Development

#### macOS
See detailed instructions in `docs/INSTALL_macOS.md`

#### Windows
See detailed instructions in `docs/INSTALL_Windows.md`

#### Linux (Debian/Ubuntu)
See detailed instructions in `docs/INSTALL_Linux.md`

### Build All Artifacts

```bash
# Check toolchain installation
./scripts/check_toolchain.sh

# Compile all F* and Dafny sources
./scripts/compile_all.sh

# Run verification checks
./scripts/verify_spec.sh
```

### Run Locally

#### Backend (Rust)
```bash
cd backend
cargo build --release
cargo run
```

#### Frontend (Next.js)
```bash
cd frontend
npm install
npm run dev
```

## Deployment

### Render (Backend)

**Configuration:**
- **Region**: Oregon (US West)
- **Root Directory**: `backend`
- **Build Command**: `cargo build --release`
- **Start Command**: `./target/release/skill-list-backend`
- **Instance Type**: Free
- **Environment Variables**:
  - `RUST_LOG=info`
  - `PORT=10000`
  - `BACKEND_ENV=production`

### Vercel (Frontend)

**Configuration:**
- **Root Directory**: `frontend`
- **Build Command**: `npm run build`
- **Output Directory**: `.next`
- **Install Command**: `npm install`
- **Environment Variables**:
  - `NEXT_PUBLIC_API_URL=https://your-render-app.onrender.com`
  - `NODE_ENV=production`

## Verification Artifacts

### F* Compilation Targets
- JavaScript (ES6+)
- CSS (verified styles)
- Svelte components
- Tailwind utilities
- HTMX endpoints
- Rust modules
- Python3 modules

### Dafny Compilation Targets
- JavaScript
- CSS
- Svelte components
- Tailwind utilities
- Alpine.js components
- HTMX endpoints
- C# classes
- Rust modules
- Python3 modules
- Mermaid diagrams

## Testing

```bash
# Backend tests
cd backend
cargo test

# Frontend tests
cd frontend
npm test

# Verification tests
./scripts/verify_spec.sh
```

## CI/CD

GitHub Actions workflows automatically:
- Verify all F* and Dafny specifications
- Compile to all target languages
- Run test suites
- Build deployment artifacts

See `.github/workflows/ci.yml` for details.

## License

MIT License - See LICENSE file for details.

## Contributing

Contributions welcome! Please see CONTRIBUTING.md for guidelines.

## Documentation

- `docs/INSTALL_macOS.md` - macOS setup instructions
- `docs/INSTALL_Windows.md` - Windows setup instructions
- `docs/INSTALL_Linux.md` - Linux setup instructions
- `docs/README_ARTIFACTS.md` - Verification artifacts documentation
- `docs/DEPLOYMENT.md` - Deployment guide

## Support

For issues and questions, please open a GitHub issue.
