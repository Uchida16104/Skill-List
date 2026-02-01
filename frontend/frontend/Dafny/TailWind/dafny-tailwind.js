// Generated from Dafny Tailwind verification
export const DafnyTailwind = {
  spacing: {
    0: 'p-0', 1: 'p-1', 2: 'p-2', 3: 'p-3', 4: 'p-4',
    5: 'p-5', 6: 'p-6', 8: 'p-8', 10: 'p-10', 12: 'p-12'
  },
  
  generateSkillCardClasses(isVerified) {
    const baseClasses = ['rounded-lg', 'shadow-md', 'p-4', 'm-2', 'border', 'transition-all'];
    const borderColor = isVerified ? 'border-green-500' : 'border-gray-300';
    const bgColor = isVerified ? 'bg-green-50' : 'bg-white';
    return [... baseClasses, borderColor, bgColor].join(' ');
  },
  
  generateBadgeClasses(type) {
    const baseClasses = ['px-2', 'py-1', 'rounded', 'text-sm', 'font-semibold'];
    const colorClasses = {
      verified: ['bg-green-100', 'text-green-800'],
      unverified: ['bg-gray-100', 'text-gray-800'],
      featured: ['bg-blue-100', 'text-blue-800']
    };
    return [...baseClasses, ...colorClasses[type]].join(' ');
  }
};
