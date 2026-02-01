// Generated from F* Tailwind verification
export const generateSkillCardClasses = (isVerified) => {
  const base = ["rounded-lg", "shadow-md", "p-4", "m-2", "border"];
  const border = isVerified ? "border-green-500" : "border-gray-300";
  return [...base, border].join(" ");
};

export const spacingScale = {
  S0: "0", S1: "1", S2: "2", S3: "3", S4: "4",
  S5: "5", S6: "6", S8: "8", S10: "10", S12: "12"
};

export const generatePaddingClass = (scale) => `p-${spacingScale[scale]}`;
export const generateMarginClass = (scale) => `m-${spacingScale[scale]}`;
