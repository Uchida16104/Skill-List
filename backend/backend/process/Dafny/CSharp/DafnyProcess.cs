// Generated from Dafny Process verification
using System;

namespace SkillList.Backend.Process
{
    public class DafnyProcess
    {
        public ulong Id { get; set; }
        public string Name { get; set; }
        public string Status { get; set; }
        public byte Priority { get; set; }
        
        public DafnyProcess(ulong id, string name, byte priority)
        {
            if (!ValidatePriority(priority))
            {
                throw new ArgumentException("Invalid priority: must be between 1 and 10");
            }
            
            Id = id;
            Name = name;
            Status = "pending";
            Priority = priority;
        }
        
        public static bool ValidatePriority(byte priority)
        {
            return priority >= 1 && priority <= 10;
        }
    }
}
