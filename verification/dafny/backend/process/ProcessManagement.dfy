// Dafny Process Management Verification

module ProcessManagement {
  datatype ProcessStatus = Pending | Running | Completed | Failed

  datatype Process = Process(
    id: nat,
    name: string,
    status: ProcessStatus,
    priority: nat
  )

  predicate ValidPriority(p: nat) {
    1 <= p <= 10
  }

  predicate ValidProcess(proc: Process) {
    ValidPriority(proc.priority) && |proc.name| > 0
  }

  method CreateProcess(id: nat, name: string, priority: nat) returns (p: Process)
    requires ValidPriority(priority)
    requires |name| > 0
    ensures ValidProcess(p)
    ensures p.id == id
    ensures p.status == Pending
  {
    p := Process(id, name, Pending, priority);
  }

  method UpdateStatus(p: Process, newStatus: ProcessStatus) returns (updated: Process)
    requires ValidProcess(p)
    ensures ValidProcess(updated)
    ensures updated.id == p.id
    ensures updated.status == newStatus
  {
    updated := p.(status := newStatus);
  }
}
