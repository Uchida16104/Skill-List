# Deployment Guide

This document provides complete deployment instructions for the Skill List application on Render (backend) and Vercel (frontend).

## Prerequisites

Before deploying, ensure you have:

1. GitHub account with repository access
2. Render account (free tier available)
3. Vercel account (free tier available)
4. All F* and Dafny sources compiled (run `./scripts/compile_all.sh`)

## Backend Deployment (Render)

### Step 1: Push to GitHub

Ensure your repository is pushed to GitHub:

```bash
git add .
git commit -m "Ready for deployment"
git push origin skill-list
```

### Step 2: Create New Web Service on Render

1. Log in to [Render Dashboard](https://dashboard.render.com/)
2. Click "New +" and select "Web Service"
3. Connect your GitHub repository
4. Select the `skill-list` branch

### Step 3: Configure Render Settings

**Basic Settings:**
- **Name**: `skill-list-backend` (or your preferred name)
- **Region**: Oregon (US West) *or any preferred region*
- **Branch**: `skill-list`
- **Root Directory**: `backend`
- **Runtime**: Rust

**Build & Deploy Settings:**
- **Build Command**: `cargo build --release`
- **Start Command**: `./target/release/skill-list-backend`

**Instance Type:**
- **Plan**: Free

**Environment Variables:**

Add the following environment variables in the Render dashboard:

```
RUST_LOG=info
PORT=10000
BACKEND_ENV=production
HOST=0.0.0.0
```

### Step 4: Deploy

1. Click "Create Web Service"
2. Render will automatically build and deploy your backend
3. Once deployed, note your backend URL (e.g., `https://skill-list-backend.onrender.com`)

### Step 5: Verify Backend Deployment

Test your backend API:

```bash
curl https://your-app-name.onrender.com/health
curl https://your-app-name.onrender.com/api/skills
```

Expected response from `/health`:
```json
{
  "status": "healthy",
  "service": "skill-list-backend",
  "version": "0.1.0"
}
```

## Frontend Deployment (Vercel)

### Step 1: Install Vercel CLI (Optional)

```bash
npm install -g vercel
```

### Step 2: Deploy via Vercel Dashboard

1. Log in to [Vercel Dashboard](https://vercel.com/dashboard)
2. Click "Add New..." and select "Project"
3. Import your GitHub repository
4. Select the `skill-list` branch

### Step 3: Configure Vercel Settings

**Framework Preset:** Next.js

**Build Settings:**
- **Root Directory**: `frontend`
- **Build Command**: `npm run build`
- **Output Directory**: `.next` (default for Next.js)
- **Install Command**: `npm install`

**Environment Variables:**

Add in the Vercel dashboard under "Environment Variables":

```
NEXT_PUBLIC_API_URL=https://your-render-app.onrender.com
NODE_ENV=production
```

Replace `your-render-app.onrender.com` with your actual Render backend URL.

### Step 4: Deploy

1. Click "Deploy"
2. Vercel will automatically build and deploy your frontend
3. Once deployed, you will receive a production URL (e.g., `https://skill-list.vercel.app`)

### Step 5: Verify Frontend Deployment

Visit your Vercel URL in a browser. You should see the Skill List application with data loaded from your Render backend.

## Alternative: Deploy via CLI

### Deploy Backend to Render via Git

Render automatically deploys when you push to your configured branch:

```bash
git add .
git commit -m "Update backend"
git push origin skill-list
```

### Deploy Frontend to Vercel via CLI

```bash
cd frontend
vercel --prod
```

Follow the prompts to complete deployment.

## Post-Deployment Configuration

### CORS Configuration

The backend is configured with permissive CORS for development. For production, update the CORS settings in `backend/src/main.rs`:

```rust
let cors = Cors::default()
    .allowed_origin("https://your-frontend-domain.vercel.app")
    .allowed_methods(vec!["GET", "POST", "PUT", "DELETE"])
    .allowed_headers(vec!["Content-Type"]);
```

### Custom Domain (Optional)

**Render:**
1. Go to your service settings
2. Add custom domain under "Custom Domains"
3. Update DNS records as instructed

**Vercel:**
1. Go to project settings
2. Navigate to "Domains"
3. Add your custom domain
4. Update DNS records as instructed

## Monitoring and Logs

### Render Logs

View real-time logs in the Render dashboard:
1. Select your service
2. Click "Logs" tab
3. Monitor application output and errors

### Vercel Logs

View deployment and runtime logs:
1. Select your project
2. Click "Deployments" tab
3. Click on a specific deployment to view logs

## Troubleshooting

### Backend Not Starting

**Issue**: Service fails to start

**Solutions**:
1. Check Render logs for compilation errors
2. Verify `Cargo.toml` dependencies are correct
3. Ensure environment variables are set
4. Check that `PORT` is set to `10000`

### Frontend Cannot Connect to Backend

**Issue**: API requests fail with CORS or network errors

**Solutions**:
1. Verify `NEXT_PUBLIC_API_URL` environment variable is correct
2. Check backend CORS configuration
3. Ensure backend service is running (check Render dashboard)
4. Test backend API directly with curl or Postman

### Build Failures

**Backend Build Fails**:
- Check Rust version compatibility
- Verify all dependencies in `Cargo.toml`
- Review build logs for specific errors

**Frontend Build Fails**:
- Check Node.js version (should be 18+)
- Verify `package.json` dependencies
- Clear build cache and retry

## Performance Optimization

### Backend Optimization

1. **Enable Release Mode**: Already configured in `Cargo.toml`
2. **Connection Pooling**: Consider implementing for database connections
3. **Caching**: Add Redis or in-memory caching for frequently accessed data

### Frontend Optimization

1. **Image Optimization**: Use Next.js Image component
2. **Code Splitting**: Leverage Next.js automatic code splitting
3. **Static Generation**: Use `getStaticProps` for static content

## Scaling

### Render Scaling

Free tier limitations:
- Service may spin down after inactivity
- Limited compute resources

To scale:
1. Upgrade to Starter plan ($7/month) for always-on service
2. Enable auto-scaling for traffic spikes
3. Add Redis for session management

### Vercel Scaling

Free tier includes:
- 100 GB bandwidth
- Unlimited deployments
- Automatic scaling

For higher traffic:
1. Upgrade to Pro plan
2. Enable Edge Functions for better global performance

## Security Considerations

1. **Environment Variables**: Never commit secrets to Git
2. **HTTPS**: Both Render and Vercel provide free SSL certificates
3. **Rate Limiting**: Implement rate limiting in backend for production
4. **Input Validation**: All inputs are validated in backend
5. **CORS**: Configure strict CORS for production

## Backup and Recovery

### Render

- Deployments are automatic from Git
- Rollback by reverting Git commit and pushing

### Vercel

- All deployments are preserved
- Rollback via dashboard by promoting a previous deployment

## Continuous Integration

GitHub Actions workflow is configured in `.github/workflows/ci.yml`:

- Runs on every push to `skill-list` branch
- Compiles F* and Dafny sources
- Builds frontend and backend
- Runs tests
- Deploys on successful build (if configured)

## Support

For deployment issues:

- **Render**: https://render.com/docs
- **Vercel**: https://vercel.com/docs
- **Project Issues**: Open an issue on GitHub

## Summary

You have successfully deployed:
- **Backend**: Rust server on Render with formally verified modules
- **Frontend**: Next.js application on Vercel with verified components
- **Verification**: F* and Dafny artifacts compiled and integrated

Your application is now live and accessible globally!
