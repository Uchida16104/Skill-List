# Deployment Configuration Summary

This document provides the exact configuration values for deploying the Skill List application to Render (backend) and Vercel (frontend).

## Render Backend Configuration

### Service Settings
- **Service Type**: Web Service
- **Name**: skill-list-backend (or your preference)
- **Region**: Oregon (US West) *recommended, or select any region*
- **Branch**: skill-list
- **Runtime**: Rust

### Build Configuration
- **Root Directory**: `backend`
- **Build Command**: `cargo build --release`
- **Start Command**: `./target/release/skill-list-backend`

### Instance Configuration
- **Instance Type**: Free
- **Auto-Deploy**: Yes (recommended)

### Environment Variables

Configure the following environment variables in the Render dashboard:

```
RUST_LOG=info
PORT=10000
BACKEND_ENV=production
HOST=0.0.0.0
```

#### Variable Descriptions:

- **RUST_LOG**: Controls logging verbosity (values: debug, info, warn, error)
- **PORT**: Port number for the server (Render requires 10000 for free tier)
- **BACKEND_ENV**: Environment identifier (production, staging, development)
- **HOST**: Bind address (0.0.0.0 allows external connections)

### Health Check Configuration
- **Health Check Path**: `/health`
- **Expected Response**: 200 OK

---

## Vercel Frontend Configuration

### Project Settings
- **Framework Preset**: Next.js
- **Name**: skill-list-frontend (or your preference)
- **Branch**: skill-list

### Build Configuration
- **Root Directory**: `frontend`
- **Build Command**: `npm run build`
- **Output Directory**: `.next` (Next.js default)
- **Install Command**: `npm install`
- **Node Version**: 18.x (automatically detected from package.json)

### Environment Variables

Configure the following environment variables in the Vercel dashboard:

```
NEXT_PUBLIC_API_URL=https://your-render-app-name.onrender.com
NODE_ENV=production
```

#### Variable Descriptions:

- **NEXT_PUBLIC_API_URL**: Full URL of your Render backend (replace with actual URL after Render deployment)
- **NODE_ENV**: Node environment (production for deployed app)

#### Important Note:
After deploying your backend to Render, you will receive a URL like `https://skill-list-backend-xxxxx.onrender.com`. Use this exact URL (including https://) as the value for `NEXT_PUBLIC_API_URL`.

### Development Environment Variables

For local development, create a `.env.local` file in the frontend directory:

```
NEXT_PUBLIC_API_URL=http://localhost:10000
NODE_ENV=development
```

This file should NOT be committed to Git (it's already in .gitignore).

---

## Deployment Workflow

### Recommended Deployment Order

1. **Deploy Backend First** (Render)
   - Push code to GitHub branch `skill-list`
   - Configure Render service as specified above
   - Wait for deployment to complete
   - Note the deployed URL

2. **Deploy Frontend Second** (Vercel)
   - Configure Vercel project as specified above
   - Add backend URL to `NEXT_PUBLIC_API_URL` environment variable
   - Deploy

### Alternative: Manual Deployment

#### Backend (Render CLI - if using render.yaml)
```bash
# Create render.yaml in project root
render deploy
```

#### Frontend (Vercel CLI)
```bash
cd frontend
vercel --prod
```

---

## Post-Deployment Verification

### Backend Health Check
```bash
curl https://your-render-app.onrender.com/health
```

Expected response:
```json
{
  "status": "healthy",
  "service": "skill-list-backend",
  "version": "0.1.0"
}
```

### Frontend Verification
1. Open your Vercel deployment URL in a browser
2. Verify the page loads without errors
3. Check that skill data appears (loaded from backend)
4. Test search and category filtering
5. Open browser console and verify no error messages

### Full Integration Test
```bash
# Test backend API directly
curl https://your-render-app.onrender.com/api/skills

# Test frontend calling backend
# Visit https://your-vercel-app.vercel.app
# Skills should load and display correctly
```

---

## Common Configuration Issues

### Issue: Frontend Cannot Connect to Backend

**Symptoms**: Empty skill list, network errors in console

**Solutions**:
1. Verify `NEXT_PUBLIC_API_URL` is set correctly in Vercel
2. Ensure URL includes `https://` protocol
3. Check backend is actually deployed and running on Render
4. Verify backend CORS settings allow your frontend domain

### Issue: Render Free Tier Spin-Down

**Symptom**: First request takes 30+ seconds

**Explanation**: Free tier services spin down after 15 minutes of inactivity

**Solutions**:
- Upgrade to Starter plan ($7/month) for always-on service
- Implement a ping service to keep it active
- Accept the delay (it's a free tier limitation)

### Issue: Build Failures

**Backend Build Fails**:
- Check Rust version in Render (should be latest stable)
- Verify Cargo.toml has correct dependencies
- Review build logs for specific error messages

**Frontend Build Fails**:
- Ensure Node version is 18 or higher
- Check package.json for dependency issues
- Verify environment variables are set correctly

---

## Security Recommendations

### Production CORS Configuration

Update `backend/src/main.rs` for production:

```rust
let cors = Cors::default()
    .allowed_origin("https://your-actual-domain.vercel.app")
    .allowed_methods(vec!["GET", "POST", "PUT", "DELETE"])
    .allowed_headers(vec!["Content-Type", "Authorization"])
    .max_age(3600);
```

### Environment Variable Security

- Never commit `.env` files to Git
- Use Render/Vercel dashboards to set sensitive values
- Rotate keys if accidentally exposed

### HTTPS Only

Both Render and Vercel provide free SSL certificates automatically. Ensure all API calls use HTTPS in production.

---

## Scaling Considerations

### Backend (Render)

**Free Tier Limits**:
- 512 MB RAM
- Shared CPU
- Spins down after inactivity

**To Scale**:
1. Upgrade to Starter ($7/month): 512 MB RAM, always-on
2. Upgrade to Standard ($25/month): 2 GB RAM, better performance
3. Add Redis for caching
4. Implement database if needed

### Frontend (Vercel)

**Free Tier Limits**:
- 100 GB bandwidth per month
- Unlimited deployments
- Serverless functions

**To Scale**:
1. Upgrade to Pro ($20/month): More bandwidth, better analytics
2. Add Edge Functions for global performance
3. Implement ISR (Incremental Static Regeneration) for better caching

---

## Monitoring and Logs

### Render Monitoring

Access logs via:
1. Render Dashboard → Your Service → Logs tab
2. Real-time log streaming
3. Search and filter capabilities

Set up alerts for:
- Service health checks failing
- High error rates
- Resource usage

### Vercel Monitoring

Access via:
1. Vercel Dashboard → Your Project → Analytics
2. Real-time visitor analytics
3. Error tracking
4. Performance metrics

---

## Rollback Procedures

### Render Rollback

1. Navigate to Render Dashboard
2. Select your service
3. Go to "Events" tab
4. Find successful deployment to rollback to
5. Click "Redeploy"

Or via Git:
```bash
git revert <commit-hash>
git push origin skill-list
```

### Vercel Rollback

1. Vercel Dashboard → Your Project → Deployments
2. Find previous successful deployment
3. Click "..." menu → "Promote to Production"

Or via CLI:
```bash
vercel rollback
```

---

## Summary

This configuration ensures:
- ✅ Free tier deployment on both platforms
- ✅ Automatic builds on Git push
- ✅ Proper environment separation (dev/prod)
- ✅ HTTPS encrypted communication
- ✅ Health monitoring and logging
- ✅ Easy rollback capabilities

For detailed step-by-step deployment instructions, see `docs/DEPLOYMENT.md`.
