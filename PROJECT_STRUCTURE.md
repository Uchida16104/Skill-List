# Project Structure Documentation

Complete overview of the Skill List project directory structure and file organization.

## Root Directory

```
skill-list-project/
├── README.md                    # Main project documentation
├── QUICKSTART.md               # Quick start guide (10-minute setup)
├── DEPLOYMENT_CONFIG.md        # Render and Vercel configuration reference
├── LICENSE                     # MIT License
├── CONTRIBUTING.md             # Contribution guidelines
├── .github/                    # GitHub Actions CI/CD
│   └── workflows/
│       └── ci.yml             # Automated build and verification
├── docs/                       # Documentation
├── scripts/                    # Build and verification scripts
├── verification/               # F* and Dafny source files
├── frontend/                   # Next.js application
└── backend/                    # Rust server
```

## Documentation (docs/)

```
docs/
├── DEPLOYMENT.md              # Complete deployment guide
├── INSTALL_macOS.md          # macOS installation instructions
├── INSTALL_Windows.md        # Windows installation instructions
├── INSTALL_Linux.md          # Linux installation instructions (Debian/Ubuntu/CentOS)
└── README_ARTIFACTS.md       # Verification artifacts documentation
```

## Scripts (scripts/)

```
scripts/
├── compile_all.sh            # Master compilation script (F* + Dafny → all targets)
├── check_toolchain.sh        # Verify installed tools
└── verify_spec.sh            # Run F* and Dafny verification
```

## Verification Sources (verification/)

### F* Sources

```
verification/fstar/
├── frontend/
│   ├── js/
│   │   └── SkillList.Frontend.JavaScript.fst
│   ├── css/
│   │   └── SkillList.Frontend.CSS.fst
│   ├── svelte/
│   │   └── SkillList.Frontend.Svelte.fst
│   ├── tailwind/
│   │   └── SkillList.Frontend.Tailwind.fst
│   └── htmx/
│       └── SkillList.Frontend.HTMX.fst
└── backend/
    ├── process/
    │   └── SkillList.Backend.Process.Rust.fst
    ├── network/
    │   └── SkillList.Backend.Network.Rust.fst
    ├── analysis/
    │   └── SkillList.Backend.Analysis.Python.fst
    └── database/
        └── (database interface specifications)
```

### Dafny Sources

```
verification/dafny/
├── frontend/
│   └── js/
│       └── SkillListDafnyJS.dfy
└── backend/
    ├── process/
    │   └── ProcessManagement.dfy
    └── network/
        └── NetworkHandling.dfy
```

## Frontend (frontend/)

```
frontend/
├── package.json               # Node.js dependencies
├── next.config.js            # Next.js configuration
├── tsconfig.json             # TypeScript configuration
├── tailwind.config.js        # Tailwind CSS configuration
├── postcss.config.js         # PostCSS configuration
├── app/                      # Next.js 14 App Router
│   ├── layout.tsx           # Root layout
│   ├── page.tsx             # Main page component
│   ├── globals.css          # Global styles
│   ├── pages/               # Additional pages
│   └── components/          # React components
├── public/                   # Static assets
└── frontend/                 # Compiled verification artifacts
    ├── Dafny/               # From Dafny compilation
    │   ├── JS/             # JavaScript modules
    │   ├── CSS/            # Style definitions
    │   ├── Svelte/         # Svelte components
    │   ├── TailWind/       # Tailwind utilities
    │   ├── AlpineJS/       # Alpine.js components
    │   └── HTMX/           # HTMX templates
    └── FStarLang/          # From F* compilation
        ├── JS/             # JavaScript modules
        ├── CSS/            # Style definitions
        ├── Svelte/         # Svelte components
        ├── TailWind/       # Tailwind utilities
        └── HTMX/           # HTMX attributes
```

## Backend (backend/)

```
backend/
├── Cargo.toml               # Rust dependencies
├── src/
│   ├── main.rs             # Main server entry point
│   ├── handlers/           # Request handlers
│   │   └── mod.rs
│   └── models/             # Data models
│       └── mod.rs
└── backend/                 # Compiled verification artifacts
    ├── process/
    │   ├── Dafny/
    │   │   ├── Mermaid/   # Process flow diagrams
    │   │   ├── CSharp/    # C# implementations
    │   │   └── Rust/      # Rust implementations
    │   └── FStarLang/
    │       ├── CSharp/    # C# implementations
    │       └── Rust/      # Rust implementations
    ├── analysis/
    │   ├── Dafny/
    │   │   ├── Mermaid/   # Analysis flow diagrams
    │   │   └── Python3/   # Python implementations
    │   └── FStarLang/
    │       └── Python3/   # Python implementations
    ├── network/
    │   ├── Dafny/
    │   │   ├── Mermaid/   # Network flow diagrams
    │   │   └── Rust/      # Rust implementations
    │   └── FStarLang/
    │       └── Rust/      # Rust implementations
    └── database/
        ├── Dafny/
        │   ├── Mermaid/   # Database flow diagrams
        │   ├── IndexedDB/ # IndexedDB interfaces
        │   ├── PouchDB/   # PouchDB interfaces
        │   ├── LocalStorage/ # LocalStorage interfaces
        │   └── SQLJS/     # SQL.js interfaces
        └── FStarLang/
            ├── IndexedDB/ # IndexedDB interfaces
            ├── PouchDB/   # PouchDB interfaces
            ├── LocalStorage/ # LocalStorage interfaces
            └── SQLJS/     # SQL.js interfaces
```

## Key Files Description

### Root Configuration Files

- **README.md**: Main project overview, architecture, and getting started guide
- **QUICKSTART.md**: Rapid setup guide for getting running in under 10 minutes
- **DEPLOYMENT_CONFIG.md**: Exact Render and Vercel configuration values
- **LICENSE**: MIT license text
- **CONTRIBUTING.md**: Guidelines for contributors

### Build Scripts

- **compile_all.sh**: Orchestrates complete build process (F* → targets, Dafny → targets, build frontend, build backend)
- **check_toolchain.sh**: Verifies Node.js, Rust, Dafny, F*, and Git are installed correctly
- **verify_spec.sh**: Runs formal verification on all F* and Dafny specifications

### Frontend Core Files

- **package.json**: Defines Next.js, React, Svelte, Alpine.js, and other frontend dependencies
- **next.config.js**: Next.js build configuration, webpack customization
- **app/page.tsx**: Main application UI with skill list display and filtering
- **app/layout.tsx**: Root layout wrapper with metadata
- **globals.css**: Global Tailwind CSS styles

### Backend Core Files

- **Cargo.toml**: Rust dependencies including actix-web, serde, tokio
- **src/main.rs**: HTTP server implementation with REST API endpoints
- **src/handlers/mod.rs**: Request handler modules (placeholder)
- **src/models/mod.rs**: Data model definitions (placeholder)

### Verification Artifacts

All compiled artifacts maintain the parent directory structure indicating their source verification language (Dafny or FStarLang) and target language.

**Frontend Artifacts**: JavaScript ES6 modules, CSS stylesheets, Svelte components, Tailwind utility functions, Alpine.js components, HTMX attribute generators

**Backend Artifacts**: Rust modules for process management and networking, C# classes for process handling, Python modules for data analysis, TypeScript interfaces for database operations, Mermaid diagrams for flow visualization

## File Count Summary

- Total Files: 39+
- F* Source Files: 7
- Dafny Source Files: 3
- Generated Artifacts: 20+
- Documentation Files: 8
- Configuration Files: 6
- Build Scripts: 3

## Technology Stack by Directory

### Frontend Technologies
- Next.js 14 (React framework)
- TypeScript (type safety)
- Tailwind CSS (styling)
- Svelte (component framework)
- Alpine.js (lightweight JavaScript)
- HTMX (HTML interactions)
- Verified artifacts from F* and Dafny

### Backend Technologies
- Rust (server runtime)
- Actix-web (web framework)
- Serde (serialization)
- Verified artifacts from F* and Dafny
- C# modules (from Dafny)
- Python modules (for analysis)

### Verification Technologies
- F* (functional verification language)
- Dafny (imperative verification language)
- Mermaid (diagram generation)

## Build Outputs

### Development Build Locations
- Frontend: `frontend/.next/` (Next.js build cache)
- Backend: `backend/target/debug/` (Rust debug build)

### Production Build Locations
- Frontend: `frontend/.next/` (optimized build)
- Backend: `backend/target/release/` (optimized Rust build)

## Deployment Artifacts

### For Render (Backend)
- Compiled binary: `backend/target/release/skill-list-backend`
- Required files: Cargo.toml, Cargo.lock, src/

### For Vercel (Frontend)
- Built application: `frontend/.next/`
- Required files: package.json, next.config.js, app/

## Version Control

### Included in Git
- All source files (F*, Dafny, Rust, TypeScript)
- Configuration files
- Documentation
- Build scripts
- Sample compiled artifacts (for reference)

### Excluded from Git (.gitignore)
- node_modules/
- .next/
- target/
- .env.local
- Large generated artifacts (regenerated during build)

## Platform-Specific Notes

### macOS Development
- Full F* and Dafny support via Homebrew
- Native Rust compilation
- M1/M2 compatibility verified

### Windows Development
- F* and Dafny via .NET SDK
- Rust via rustup-init.exe
- Git Bash recommended for script execution

### Linux Development  
- Full support on Debian, Ubuntu, CentOS
- Package manager installation for all tools
- Native performance for compilation

This structure ensures clear separation of concerns, reproducible builds across platforms, and maintainable verification artifacts integrated into a modern full-stack application.
