import type { Metadata } from 'next';
import './globals.css';

export const metadata: Metadata = {
  title: 'Skill List - Formally Verified Portfolio',
  description: 'Full-stack application with F* and Dafny formal verification',
};

export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
