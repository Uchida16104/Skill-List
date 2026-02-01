/** @type {import('tailwindcss').Config} */
module.exports = {
  content: [
    './pages/**/*.{js,ts,jsx,tsx,mdx}',
    './components/**/*.{js,ts,jsx,tsx,mdx}',
    './app/**/*.{js,ts,jsx,tsx,mdx}',
    './frontend/**/*.{js,ts,jsx,tsx,mdx,svelte}',
  ],
  theme: {
    extend: {
      colors: {
        'skill-verified': '#10b981',
        'skill-unverified': '#6b7280',
      },
    },
  },
  plugins: [],
}
