# Quick Start Guide

Get the Skill List application running in under 10 minutes.

## Prerequisites Checklist

- [ ] Node.js 18+ installed
- [ ] Rust 1.70+ installed
- [ ] Git installed
- [ ] 5GB free disk space

## Installation (3 minutes)

```bash
# Clone repository
git clone https://github.com/Uchida16104/Skill-List.git
cd Skill-List
git checkout -b skill-list

# Verify tools
./scripts/check_toolchain.sh

# Compile all verification artifacts
./scripts/compile_all.sh
```

## Run Locally (2 minutes)

### Terminal 1 - Backend
```bash
cd backend
cargo run --release
# Wait for: "Listening on 0.0.0.0:10000"
```

### Terminal 2 - Frontend
```bash
cd frontend
npm install
npm run dev
# Wait for: "Ready on http://localhost:3000"
```

### Open Browser
Navigate to: http://localhost:3000

You should see the Skill List application with sample data.

## Deploy to Production (5 minutes)

### Backend to Render
1. Push code to GitHub
2. Create new Web Service on Render
3. Configure:
   - Root Directory: `backend`
   - Build: `cargo build --release`
   - Start: `./target/release/skill-list-backend`
   - Environment: `PORT=10000`, `RUST_LOG=info`

### Frontend to Vercel
1. Import project from GitHub
2. Configure:
   - Root Directory: `frontend`
   - Build: `npm run build`
   - Environment: `NEXT_PUBLIC_API_URL=<your-render-url>`

Done! Your application is live.

## Troubleshooting

**Backend won't start?**
- Check Rust is installed: `cargo --version`
- Check port 10000 is free: `lsof -i :10000` (macOS/Linux)

**Frontend won't start?**
- Check Node.js: `node --version` (need 18+)
- Delete node_modules and retry: `rm -rf node_modules && npm install`

**Can't see data?**
- Ensure backend is running on port 10000
- Check NEXT_PUBLIC_API_URL in frontend/.env.local

## Next Steps

- Read full documentation in `docs/`
- Explore F* sources in `verification/fstar/`
- Explore Dafny sources in `verification/dafny/`
- Run verification: `./scripts/verify_spec.sh`
- Deploy following `docs/DEPLOYMENT.md`

## Support

- Documentation: See `docs/` folder
- Issues: GitHub Issues
- Deployment: `docs/DEPLOYMENT.md`
