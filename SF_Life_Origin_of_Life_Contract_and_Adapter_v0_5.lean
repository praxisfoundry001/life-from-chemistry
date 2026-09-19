/-
STRUCTURAL FLOW — LIFE / ORIGIN-OF-LIFE CONTRACT AND ADAPTER COMPANION v0.5

BUILD ROLE
----------
Append-only scoped companion for the unchanged current Structural Flow
Universal Kernel.

This file carries the twice-machine-clean SF Life checkpoint verbatim, then
adds AMC, OCTT, and the public Universal Translation Contract adapter.

Do not append the earlier standalone Life checkpoint or standalone AMC scaffold
when running this file; their contents are already carried here.
-/

namespace StructuralFlow
namespace LifeChemistry

open PlusThree

/-! --------------------------------------------------------------------------
Scoped Life vocabulary
---------------------------------------------------------------------------- -/

inductive LifeCandidate where
  | life
deriving DecidableEq, Repr

inductive LifeJob where
  | maintenanceBearingContinuation
deriving DecidableEq, Repr

inductive LifeShape where
  | selfDefendingBoundaryRegime
deriving DecidableEq, Repr

inductive LifeCapacity where
  | viableContinuation
deriving DecidableEq, Repr

inductive LifeCase where
  | holding
  | failure
deriving DecidableEq, Repr

/-!
Level and Scope are intentionally generic parameters.

A Life world cannot be instantiated without an explicit selected level and
scope.  This is the machine-side form of:

  "No level, no threshold claim."
-/

/-! --------------------------------------------------------------------------
Lower semantics for the +3 object
---------------------------------------------------------------------------- -/

def lifeStructuralJob
    {Level Scope : Type}
    (selectedLevel : Level)
    (selectedScope : Scope) :
    LifeCandidate → Level → Scope → LifeJob → Prop :=
  fun candidate level scope job =>
    candidate = LifeCandidate.life
    ∧ level = selectedLevel
    ∧ scope = selectedScope
    ∧ job = LifeJob.maintenanceBearingContinuation

def lifeHonestShape
    {Level Scope : Type}
    (selectedLevel : Level)
    (selectedScope : Scope) :
    LifeCandidate → Level → Scope → LifeShape → Prop :=
  fun candidate level scope shape =>
    candidate = LifeCandidate.life
    ∧ level = selectedLevel
    ∧ scope = selectedScope
    ∧ shape = LifeShape.selfDefendingBoundaryRegime

def lifePerforms :
    LifeShape → LifeJob → Prop :=
  fun shape job =>
    shape = LifeShape.selfDefendingBoundaryRegime
    ∧ job = LifeJob.maintenanceBearingContinuation

/-
No strictly thinner Life shape is installed in this scoped checkpoint.
If a thinner same-job shape is later earned, this definition must reopen.
-/
def lifeStrictlyThinner :
    LifeShape → LifeShape → Prop :=
  fun _ _ => False

def lifeCaseInScope
    {Level Scope : Type}
    (selectedLevel : Level)
    (selectedScope : Scope) :
    LifeCandidate → Level → Scope → LifeCase → Prop :=
  fun candidate level scope _case =>
    candidate = LifeCandidate.life
    ∧ level = selectedLevel
    ∧ scope = selectedScope

def lifeShapeHolds :
    LifeShape → LifeCase → Prop :=
  fun shape case =>
    shape = LifeShape.selfDefendingBoundaryRegime
    ∧ case = LifeCase.holding

def lifeFailurePassage :
    LifeCase → LifeCase → Prop :=
  fun before after =>
    before = LifeCase.holding
    ∧ after = LifeCase.failure

def lifeShapeFails :
    LifeShape → LifeCase → Prop :=
  fun shape case =>
    shape = LifeShape.selfDefendingBoundaryRegime
    ∧ case = LifeCase.failure

def lifeCapacityAvailable :
    LifeCapacity → LifeCase → Prop :=
  fun capacity case =>
    capacity = LifeCapacity.viableContinuation
    ∧ case = LifeCase.holding

/-! --------------------------------------------------------------------------
False-substitute witness: activity can survive Life-capacity failure
---------------------------------------------------------------------------- -/

/-
This is deliberately weak.

It machine-encodes only the governing discrimination:
  Activity is not Life.

It does not assert that every Life failure retains activity.
-/
def ChemicalActivity : LifeCase → Prop :=
  fun _ => True

/-! --------------------------------------------------------------------------
Current scoped Life world
---------------------------------------------------------------------------- -/

def lifeWorld
    {Level Scope : Type}
    (selectedLevel : Level)
    (selectedScope : Scope) :
    PlusThree.World
      LifeCandidate
      Level
      Scope
      LifeJob
      LifeShape
      LifeCapacity
      LifeCase
    where

  selectedCandidate := LifeCandidate.life
  selectedLevel := selectedLevel
  selectedScope := selectedScope

  selectedJob := LifeJob.maintenanceBearingContinuation
  selectedShape := LifeShape.selfDefendingBoundaryRegime
  selectedCapacity := LifeCapacity.viableContinuation

  structuralJob :=
    lifeStructuralJob selectedLevel selectedScope

  honestShape :=
    lifeHonestShape selectedLevel selectedScope

  performs := lifePerforms
  strictlyThinner := lifeStrictlyThinner

  caseInScope :=
    lifeCaseInScope selectedLevel selectedScope

  shapeHolds := lifeShapeHolds
  failurePassage := lifeFailurePassage
  shapeFails := lifeShapeFails
  capacityAvailable := lifeCapacityAvailable

  /-
  These six booleans record the current scoped companion's completed
  discrimination posture.  Later pressure may reopen any of them.
  -/
  adjacentAbsorptionTested := True
  falseSubstituteTested := True
  levelShiftTested := True
  scopeShiftTested := True
  internalInflationTested := True
  neededAtAllTested := True

  /-
  Imported scoped-authority pins.
  Not inferred from SieveComplete.
  -/
  candidateSurvives := True
  objectClosed := True

/-! --------------------------------------------------------------------------
Q1 — Job
---------------------------------------------------------------------------- -/

theorem life_job_fidelity
    {Level Scope : Type}
    (level : Level)
    (scope : Scope) :
    PlusThree.JobFidelity (lifeWorld level scope) := by
  simp
    [PlusThree.JobFidelity,
     lifeWorld,
     lifeStructuralJob]

/-! --------------------------------------------------------------------------
Q2 — Weakest honest shape
---------------------------------------------------------------------------- -/

theorem life_shape_fidelity
    {Level Scope : Type}
    (level : Level)
    (scope : Scope) :
    PlusThree.ShapeFidelity (lifeWorld level scope) := by
  simp
    [PlusThree.ShapeFidelity,
     PlusThree.MinimalHonestShapeAt,
     lifeWorld,
     lifeHonestShape,
     lifePerforms,
     lifeStrictlyThinner]

/-! --------------------------------------------------------------------------
Q3 — Capacity lost if the selected Life shape fails
---------------------------------------------------------------------------- -/

theorem life_capacity_loss_fidelity
    {Level Scope : Type}
    (level : Level)
    (scope : Scope) :
    PlusThree.CapacityLossFidelity (lifeWorld level scope) := by
  refine
    ⟨LifeCase.holding,
     LifeCase.failure,
     ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [lifeWorld, lifeCaseInScope]
  · simp [lifeWorld, lifeCaseInScope]
  · simp [lifeWorld, lifeShapeHolds]
  · simp [lifeWorld, lifeCapacityAvailable]
  · simp [lifeWorld, lifeFailurePassage]
  · simp [lifeWorld, lifeShapeFails]
  · simp [lifeWorld, lifeCapacityAvailable]

/-! --------------------------------------------------------------------------
+3 endpoint and pressure completion
---------------------------------------------------------------------------- -/

theorem life_object_answer_endpoint
    {Level Scope : Type}
    (level : Level)
    (scope : Scope) :
    PlusThree.ObjectAnswerEndpoint (lifeWorld level scope) := by
  exact
    (PlusThree.object_answer_endpoint_iff_plus_three
      (lifeWorld level scope)).mpr
      ⟨life_job_fidelity level scope,
       life_shape_fidelity level scope,
       life_capacity_loss_fidelity level scope⟩

theorem life_pressure_adjudicated
    {Level Scope : Type}
    (level : Level)
    (scope : Scope) :
    PlusThree.PressureAdjudicated (lifeWorld level scope) := by
  simp [PlusThree.PressureAdjudicated, lifeWorld]

theorem life_sieve_complete
    {Level Scope : Type}
    (level : Level)
    (scope : Scope) :
    PlusThree.SieveComplete (lifeWorld level scope) := by
  exact
    ⟨life_object_answer_endpoint level scope,
     life_pressure_adjudicated level scope⟩

/-! --------------------------------------------------------------------------
Explicit "Activity is not Life" discrimination
---------------------------------------------------------------------------- -/

theorem activity_survives_selected_life_failure :
    ChemicalActivity LifeCase.failure := by
  simp [ChemicalActivity]

theorem selected_life_capacity_absent_after_failure :
    ¬ lifeCapacityAvailable
        LifeCapacity.viableContinuation
        LifeCase.failure := by
  simp [lifeCapacityAvailable]

theorem activity_does_not_suffice_for_selected_life_capacity :
    ∃ case : LifeCase,
      ChemicalActivity case
      ∧
      ¬ lifeCapacityAvailable
          LifeCapacity.viableContinuation
          case := by
  exact
    ⟨LifeCase.failure,
     activity_survives_selected_life_failure,
     selected_life_capacity_absent_after_failure⟩

/-! --------------------------------------------------------------------------
Imported scoped-authority pins
---------------------------------------------------------------------------- -/

theorem current_scoped_life_candidate_survives
    {Level Scope : Type}
    (level : Level)
    (scope : Scope) :
    (lifeWorld level scope).candidateSurvives := by
  simp [lifeWorld]

theorem current_scoped_life_object_marked_closed
    {Level Scope : Type}
    (level : Level)
    (scope : Scope) :
    (lifeWorld level scope).objectClosed := by
  simp [lifeWorld]

/-! --------------------------------------------------------------------------
Machine checkpoint
---------------------------------------------------------------------------- -/

/-
Interpretation:

1. The current scoped Life object has coherent +3 answers at any explicitly
   declared level and scope.

2. The selected failure witness can retain chemical activity while losing the
   selected Life capacity, so activity is not sufficient for Life.

3. The current human-semantic scoped authority marks the candidate as survived
   and closed.

4. This theorem does NOT derive empirical Life, AMC, OCTT, reproduction,
   evolution, or strict identity.
-/
theorem life_object_machine_checkpoint
    {Level Scope : Type}
    (level : Level)
    (scope : Scope) :
    PlusThree.SieveComplete (lifeWorld level scope)
    ∧ (lifeWorld level scope).candidateSurvives
    ∧ (lifeWorld level scope).objectClosed
    ∧ ChemicalActivity LifeCase.failure
    ∧
      ¬ lifeCapacityAvailable
          LifeCapacity.viableContinuation
          LifeCase.failure := by
  exact
    ⟨life_sieve_complete level scope,
     current_scoped_life_candidate_survives level scope,
     current_scoped_life_object_marked_closed level scope,
     activity_survives_selected_life_failure,
     selected_life_capacity_absent_after_failure⟩

end LifeChemistry
end StructuralFlow

/-!
===============================================================================
LIFE / ORIGIN-OF-LIFE CONTRACT AND PUBLIC-KERNEL ADAPTER COMPANION v0.1
===============================================================================

EXECUTION
---------
Append this entire file directly BELOW the unchanged current Structural Flow
Universal Kernel in the Lean browser.

No import line is used.

This file is self-contained relative to the already-loaded Universal Kernel.
It does NOT depend on the earlier standalone Life checkpoint file or the
superseded standalone AMC scaffold.

ARCHITECTURE
------------
Seat 1  — confirmed scoped SF Life object (carried above verbatim from the
          twice-clean Life checkpoint);
Seat 2  — field-native Autonomous Maintenance Core (AMC) admission contract;
Seat 3  — Organizational Continuity Through Turnover Test (OCTT) evidence
          contract;
Seat 4  — public Universal Translation Contract adapter from the current
          origin-of-life science state toward the scoped SF Life object;
Seat 5  — combined machine checkpoint.

CURRENT SCIENCE STATE
---------------------
Life object:
  machine-confirmed at the scoped +3 level.

AMC:
  adjudication procedure formalized;
  no real chemical system is encoded here as AMC-positive.

OCTT:
  adjudication procedure formalized;
  no real experiment is encoded here as executed.

AMC -> SF Life translation:
  NOT YET ADJUDICABLE at the current evidence state because the empirical
  carrier, level, scope, structural-preservation, and AMC-entry burdens remain
  open.

A clean Lean elaboration certifies only the encoded contract architecture.
It does not create empirical evidence.
===============================================================================
-/

namespace StructuralFlow
namespace OriginOfLifeAMC

universe u

/-! --------------------------------------------------------------------------
AMC evidence grammar
---------------------------------------------------------------------------- -/

inductive EvidenceState where
  | discharged
  | violated
  | open
deriving DecidableEq, Repr

inductive Burden where
  | pins
  | controlEfficacy
  | endogeneity
  | mutualIntegration
  | regeneration
  | continuedOrganizationalCompetence
  | assayAdequacy
deriving DecidableEq, Repr

def SubstantiveBurden : Burden -> Prop
  | .controlEfficacy => True
  | .endogeneity => True
  | .mutualIntegration => True
  | .regeneration => True
  | .continuedOrganizationalCompetence => True
  | .pins => False
  | .assayAdequacy => False

/-! --------------------------------------------------------------------------
Declared empirical surface
---------------------------------------------------------------------------- -/

structure Pins
    (System Environment Level Scope Horizon Boundary Process Control : Type u)
    where
  system : System
  environment : Environment
  level : Level
  scope : Scope
  horizon : Horizon
  boundary : Boundary
  processes : Process -> Prop
  controls : Control -> Prop

structure World
    (System Environment Level Scope Horizon Boundary Process Control : Type u)
    where
  pins :
    Pins System Environment Level Scope Horizon Boundary Process Control

  state :
    Burden -> EvidenceState

  evidence :
    Burden -> EvidenceState -> Prop

  warrant :
    ∀ b,
      evidence b (state b)

/-! --------------------------------------------------------------------------
AMC headline dispositions
---------------------------------------------------------------------------- -/

/--
AMC POSITIVE:

All constitutive burdens AMC-0 through AMC-6 are discharged.
-/
def AMCPositive
    {System Environment Level Scope Horizon Boundary Process Control : Type u}
    (w :
      World System Environment Level Scope Horizon Boundary Process Control) :
    Prop :=
  ∀ b : Burden,
    w.state b = EvidenceState.discharged

/--
AMC NEGATIVE:

Negative standing requires adequate pinning, adequate assay, and an actual
violation of one substantive maintenance burden AMC-1 through AMC-5.

Pinning failure or assay inadequacy never counts as evidence that autonomous
maintenance is absent.
-/
def AMCNegative
    {System Environment Level Scope Horizon Boundary Process Control : Type u}
    (w :
      World System Environment Level Scope Horizon Boundary Process Control) :
    Prop :=
  w.state Burden.pins = EvidenceState.discharged
  ∧
  w.state Burden.assayAdequacy = EvidenceState.discharged
  ∧
  ∃ b : Burden,
    SubstantiveBurden b
    ∧
    w.state b = EvidenceState.violated

/--
AMC INDETERMINATE:

Every world that is neither positively admitted nor adequately shown negative.
-/
def AMCIndeterminate
    {System Environment Level Scope Horizon Boundary Process Control : Type u}
    (w :
      World System Environment Level Scope Horizon Boundary Process Control) :
    Prop :=
  ¬ AMCPositive w
  ∧
  ¬ AMCNegative w

theorem amc_negative_not_positive
    {System Environment Level Scope Horizon Boundary Process Control : Type u}
    {w :
      World System Environment Level Scope Horizon Boundary Process Control}
    (hNeg : AMCNegative w) :
    ¬ AMCPositive w := by
  intro hPos
  rcases hNeg with
    ⟨_hPins, _hAssay, b, _hSubstantive, hViolated⟩
  have hDischarged :
      w.state b = EvidenceState.discharged :=
    hPos b
  rw [hDischarged] at hViolated
  cases hViolated

theorem amc_positive_not_negative
    {System Environment Level Scope Horizon Boundary Process Control : Type u}
    {w :
      World System Environment Level Scope Horizon Boundary Process Control}
    (hPos : AMCPositive w) :
    ¬ AMCNegative w := by
  intro hNeg
  exact (amc_negative_not_positive hNeg) hPos

theorem pins_not_discharged_blocks_positive
    {System Environment Level Scope Horizon Boundary Process Control : Type u}
    {w :
      World System Environment Level Scope Horizon Boundary Process Control}
    (hPins :
      w.state Burden.pins ≠ EvidenceState.discharged) :
    ¬ AMCPositive w := by
  intro hPos
  exact hPins (hPos Burden.pins)

theorem assay_not_discharged_blocks_positive
    {System Environment Level Scope Horizon Boundary Process Control : Type u}
    {w :
      World System Environment Level Scope Horizon Boundary Process Control}
    (hAssay :
      w.state Burden.assayAdequacy ≠ EvidenceState.discharged) :
    ¬ AMCPositive w := by
  intro hPos
  exact hAssay (hPos Burden.assayAdequacy)

theorem amc_headline_coverage
    {System Environment Level Scope Horizon Boundary Process Control : Type u}
    (w :
      World System Environment Level Scope Horizon Boundary Process Control) :
    AMCNegative w
    ∨ AMCIndeterminate w
    ∨ AMCPositive w := by
  classical
  by_cases hPos : AMCPositive w
  · exact Or.inr (Or.inr hPos)
  · by_cases hNeg : AMCNegative w
    · exact Or.inl hNeg
    · exact Or.inr (Or.inl ⟨hPos, hNeg⟩)

/-! --------------------------------------------------------------------------
Synthetic contract witnesses
---------------------------------------------------------------------------- -/

def demoPins :
    Pins Unit Unit Unit Unit Unit Unit Unit Unit
    where
  system := ()
  environment := ()
  level := ()
  scope := ()
  horizon := ()
  boundary := ()
  processes := fun _ => True
  controls := fun _ => True

def demoEvidence :
    Burden -> EvidenceState -> Prop :=
  fun _ _ => True

def positiveDemo :
    World Unit Unit Unit Unit Unit Unit Unit Unit
    where
  pins := demoPins
  state := fun _ => EvidenceState.discharged
  evidence := demoEvidence
  warrant := by
    intro b
    simp [demoEvidence]

def negativeDemoState :
    Burden -> EvidenceState
  | .endogeneity => EvidenceState.violated
  | _ => EvidenceState.discharged

def negativeDemo :
    World Unit Unit Unit Unit Unit Unit Unit Unit
    where
  pins := demoPins
  state := negativeDemoState
  evidence := demoEvidence
  warrant := by
    intro b
    simp [demoEvidence]

def indeterminateDemoState :
    Burden -> EvidenceState
  | .pins => EvidenceState.open
  | _ => EvidenceState.discharged

def indeterminateDemo :
    World Unit Unit Unit Unit Unit Unit Unit Unit
    where
  pins := demoPins
  state := indeterminateDemoState
  evidence := demoEvidence
  warrant := by
    intro b
    simp [demoEvidence]

theorem positive_demo_is_positive :
    AMCPositive positiveDemo := by
  intro b
  rfl

theorem negative_demo_is_negative :
    AMCNegative negativeDemo := by
  refine
    ⟨rfl, rfl,
     Burden.endogeneity,
     ?_, rfl⟩
  simp [SubstantiveBurden]

theorem indeterminate_demo_not_positive :
    ¬ AMCPositive indeterminateDemo := by
  intro hPos
  have h :=
    hPos Burden.pins
  simp [indeterminateDemo, indeterminateDemoState] at h

theorem indeterminate_demo_not_negative :
    ¬ AMCNegative indeterminateDemo := by
  intro hNeg
  exact
    (by
      have hPins :=
        hNeg.1
      simp [indeterminateDemo, indeterminateDemoState] at hPins)

theorem indeterminate_demo_is_indeterminate :
    AMCIndeterminate indeterminateDemo := by
  exact
    ⟨indeterminate_demo_not_positive,
     indeterminate_demo_not_negative⟩

theorem amc_domain_contract_machine_checkpoint :
    AMCPositive positiveDemo
    ∧ AMCNegative negativeDemo
    ∧ AMCIndeterminate indeterminateDemo
    ∧ (∀
        {System Environment Level Scope Horizon Boundary Process Control : Type u}
        (w :
          World
            System Environment Level Scope Horizon Boundary Process Control),
        AMCNegative w
        ∨ AMCIndeterminate w
        ∨ AMCPositive w) := by
  refine
    ⟨positive_demo_is_positive,
     negative_demo_is_negative,
     indeterminate_demo_is_indeterminate,
     ?_⟩
  intro
    System Environment Level Scope Horizon Boundary Process Control w
  exact amc_headline_coverage w

end OriginOfLifeAMC
end StructuralFlow


namespace StructuralFlow
namespace OriginOfLifeOCTT

open OriginOfLifeAMC

/-! --------------------------------------------------------------------------
OCTT evidence grammar
---------------------------------------------------------------------------- -/

inductive Burden where
  | sourceAgeResolution
  | carrierAncestryResolution
  | passiveSeedExclusion
  | maintenanceFunction
  | assayAdequacy
deriving DecidableEq, Repr

inductive ContinuityClass where
  | continuousBoundedCarry
  | daughterLineageCarry
  | deNovoNucleation
  | dissolutionReconstitution
  | populationPropagation
  | indeterminate
deriving DecidableEq, Repr

structure World where
  state :
    Burden -> EvidenceState

  evidence :
    Burden -> EvidenceState -> Prop

  warrant :
    ∀ b,
      evidence b (state b)

  continuity :
    ContinuityClass

def AllBurdensDischarged
    (w : World) :
    Prop :=
  ∀ b : Burden,
    w.state b = EvidenceState.discharged

def CarrierContinuityPositive
    (w : World) :
    Prop :=
  AllBurdensDischarged w
  ∧ w.continuity = ContinuityClass.continuousBoundedCarry

def LineageContinuityPositive
    (w : World) :
    Prop :=
  AllBurdensDischarged w
  ∧ w.continuity = ContinuityClass.daughterLineageCarry

def NewCarrierProduction
    (w : World) :
    Prop :=
  AllBurdensDischarged w
  ∧ w.continuity = ContinuityClass.deNovoNucleation

def Reconstitution
    (w : World) :
    Prop :=
  AllBurdensDischarged w
  ∧ w.continuity = ContinuityClass.dissolutionReconstitution

def PopulationPropagation
    (w : World) :
    Prop :=
  AllBurdensDischarged w
  ∧ w.continuity = ContinuityClass.populationPropagation

def OCTTIndeterminate
    (w : World) :
    Prop :=
  (∃ b : Burden,
      w.state b ≠ EvidenceState.discharged)
  ∨ w.continuity = ContinuityClass.indeterminate

/-! --------------------------------------------------------------------------
Synthetic witnesses
---------------------------------------------------------------------------- -/

def demoEvidence :
    Burden -> EvidenceState -> Prop :=
  fun _ _ => True

def carrierPositiveDemo :
    World where
  state := fun _ => EvidenceState.discharged
  evidence := demoEvidence
  warrant := by
    intro b
    simp [demoEvidence]
  continuity := ContinuityClass.continuousBoundedCarry

def lineagePositiveDemo :
    World where
  state := fun _ => EvidenceState.discharged
  evidence := demoEvidence
  warrant := by
    intro b
    simp [demoEvidence]
  continuity := ContinuityClass.daughterLineageCarry

def indeterminateDemoState :
    Burden -> EvidenceState
  | .sourceAgeResolution => EvidenceState.open
  | _ => EvidenceState.discharged

def indeterminateDemo :
    World where
  state := indeterminateDemoState
  evidence := demoEvidence
  warrant := by
    intro b
    simp [demoEvidence]
  continuity := ContinuityClass.indeterminate

theorem carrier_positive_demo :
    CarrierContinuityPositive carrierPositiveDemo := by
  constructor
  · intro b
    rfl
  · rfl

theorem lineage_positive_demo :
    LineageContinuityPositive lineagePositiveDemo := by
  constructor
  · intro b
    rfl
  · rfl

theorem octt_indeterminate_demo :
    OCTTIndeterminate indeterminateDemo := by
  exact
    Or.inl
      ⟨Burden.sourceAgeResolution,
       by
         simp [indeterminateDemo, indeterminateDemoState]⟩

/--
Critical internal firewall:

A clean carrier-continuity OCTT result does not, by itself, imply AMC POSITIVE.

The synthetic witness pairs a fully discharged C1 OCTT world with an AMC world
whose pinning burden remains open.
-/
theorem octt_does_not_by_itself_close_amc :
    CarrierContinuityPositive carrierPositiveDemo
    ∧ OriginOfLifeAMC.AMCIndeterminate
        OriginOfLifeAMC.indeterminateDemo := by
  exact
    ⟨carrier_positive_demo,
     OriginOfLifeAMC.indeterminate_demo_is_indeterminate⟩

theorem octt_contract_machine_checkpoint :
    CarrierContinuityPositive carrierPositiveDemo
    ∧ LineageContinuityPositive lineagePositiveDemo
    ∧ OCTTIndeterminate indeterminateDemo
    ∧ OriginOfLifeAMC.AMCIndeterminate
        OriginOfLifeAMC.indeterminateDemo := by
  exact
    ⟨carrier_positive_demo,
     lineage_positive_demo,
     octt_indeterminate_demo,
     OriginOfLifeAMC.indeterminate_demo_is_indeterminate⟩

end OriginOfLifeOCTT
end StructuralFlow


/-!
===============================================================================
LIFE / ORIGIN-OF-LIFE -> PUBLIC UNIVERSAL TRANSLATION CONTRACT ADAPTER v0.1
===============================================================================

Purpose
-------
Route the CURRENT origin-of-life science state through the public Universal
Translation Contract without modifying the Universal Kernel.

Current state:
  * scoped SF Life object: located / machine-confirmed;
  * origin-of-life chemistry surface: independently warranted;
  * no target empirical carrier has yet been executed through OCTT / AMC;
  * AMC empirical entry: OPEN;
  * source/carrier pin, level pin, scope pin, and structural-preservation
    burdens for a real target: OPEN;
  * no required burden is encoded as violated.

Expected disposition:
  NOT YET ADJUDICABLE.

This is the correct pre-experiment machine state.
===============================================================================
-/

namespace StructuralFlow
namespace LifeOriginPublicKernelAdapter

open UniversalTranslationContract
open LifeChemistry
open OriginOfLifeAMC
open OriginOfLifeOCTT

/-! --------------------------------------------------------------------------
Life-specific public translation burdens
---------------------------------------------------------------------------- -/

inductive ObjectBurden where
  | jobLocated
  | shapeLocated
  | lossLocated
  | activityFalseSubstituteCleared
  | sameLevelNonAbsorption
  | boundedCarrierRealization
  | internallyCarriedMaintenance
  | continuationPreservation
  | failureDiscrimination
deriving DecidableEq, Repr

inductive DomainBurden where
  | amcEmpiricalAdmission
deriving DecidableEq, Repr

/-! --------------------------------------------------------------------------
Current core states
---------------------------------------------------------------------------- -/

def coreState : CoreBurden -> Disposition
  | .surfaceWarrant => .discharged
  | .sourceCarrierPin => .open
  | .objectPin => .discharged
  | .levelPin => .open
  | .scopePin => .open
  | .structuralPreservation => .open
  | .nonCircularity => .discharged
  | .identityFirewall => .discharged

/-! --------------------------------------------------------------------------
Current Life-object states
---------------------------------------------------------------------------- -/

def objectRequired (_ : ObjectBurden) : Prop := True

def objectState : ObjectBurden -> Disposition
  | .jobLocated => .discharged
  | .shapeLocated => .discharged
  | .lossLocated => .discharged
  | .activityFalseSubstituteCleared => .discharged
  | .sameLevelNonAbsorption => .discharged
  | .boundedCarrierRealization => .open
  | .internallyCarriedMaintenance => .open
  | .continuationPreservation => .open
  | .failureDiscrimination => .open

/-! --------------------------------------------------------------------------
Current domain states
---------------------------------------------------------------------------- -/

def domainEntryRequired : DomainBurden -> Prop
  | .amcEmpiricalAdmission => True

def domainDownstreamRequired : DomainBurden -> Prop
  | .amcEmpiricalAdmission => False

def domainState : DomainBurden -> Disposition
  | .amcEmpiricalAdmission => .open

/-! --------------------------------------------------------------------------
Public Universal Translation Contract packet
---------------------------------------------------------------------------- -/

noncomputable def lifeOriginPublicWorld :
    UniversalTranslationContract.World ObjectBurden DomainBurden where

  coreState := coreState
  coreEvidence := fun b state => state = coreState b
  coreWarrant := by
    intro b
    rfl

  objectRequired := objectRequired
  objectState := objectState
  objectEvidence := fun b state => state = objectState b
  objectWarrant := by
    intro b _
    rfl

  domainEntryRequired := domainEntryRequired
  domainDownstreamRequired := domainDownstreamRequired
  domainRoleDisjoint := by
    intro b
    cases b <;>
      simp [domainEntryRequired, domainDownstreamRequired]

  domainState := domainState
  domainEvidence := fun b state => state = domainState b
  domainWarrant := by
    intro b _
    rfl

/-! --------------------------------------------------------------------------
Current exact public-kernel disposition
---------------------------------------------------------------------------- -/

/--
No required burden is currently encoded as violated.

Open means not yet adjudicated, not failed.
-/
theorem current_packet_has_no_known_failure :
    ¬ Nonempty
      (UniversalTranslationContract.KnownFailure lifeOriginPublicWorld) := by
  intro h
  rcases h with ⟨failure⟩
  cases failure with
  | core burden failed =>
      cases burden <;>
        simp [lifeOriginPublicWorld, coreState] at failed
  | object burden _ failed =>
      cases burden <;>
        simp [lifeOriginPublicWorld, objectState] at failed
  | domainEntry burden _ failed =>
      cases burden <;>
        simp [lifeOriginPublicWorld, domainState] at failed

/--
Exact located open certificate:
the empirical AMC admission has not yet been discharged.
-/
def amcEntryOpen :
    UniversalTranslationContract.KnownOpen lifeOriginPublicWorld :=
  UniversalTranslationContract.KnownOpen.domainEntry
    DomainBurden.amcEmpiricalAdmission
    (by
      simp [lifeOriginPublicWorld, domainEntryRequired])
    (by
      simp [lifeOriginPublicWorld, domainState])

theorem life_origin_public_kernel_not_yet_adjudicable :
    UniversalTranslationContract.NotYetAdjudicable
      lifeOriginPublicWorld := by
  constructor
  · exact current_packet_has_no_known_failure
  · exact ⟨amcEntryOpen⟩

theorem life_origin_public_kernel_not_structural_conforms :
    ¬ UniversalTranslationContract.StructuralConforms
        lifeOriginPublicWorld := by
  simpa [UniversalTranslationContract.StructuralConforms] using
    (UniversalTranslationContract.knownOpen_blocks_gatingPass
      amcEntryOpen)

/-! --------------------------------------------------------------------------
Explicit machine firewalls
---------------------------------------------------------------------------- -/

/--
AMC contract closure is not empirical AMC satisfaction.
-/
theorem amc_contract_checkpoint_does_not_supply_empirical_entry :
    domainState DomainBurden.amcEmpiricalAdmission = Disposition.open := by
  rfl

/--
OCTT contract closure is not AMC admission.
-/
theorem octt_contract_checkpoint_does_not_supply_amc_entry :
    OriginOfLifeOCTT.CarrierContinuityPositive
      OriginOfLifeOCTT.carrierPositiveDemo
    ∧ domainState DomainBurden.amcEmpiricalAdmission = Disposition.open := by
  exact
    ⟨OriginOfLifeOCTT.carrier_positive_demo, rfl⟩

/--
Material-turnover continuity is not used as a strict-identity proof.

The current public adapter keeps the identity firewall discharged precisely
because the translation does not infer strict identity from turnover or lineage.
-/
theorem identity_firewall_currently_discharged :
    coreState CoreBurden.identityFirewall = Disposition.discharged := by
  rfl

/-! --------------------------------------------------------------------------
Combined companion machine checkpoint
---------------------------------------------------------------------------- -/

/--
One clean theorem witnesses the current whole companion posture:

  Life object:
    +3 / pressure checkpoint clean;

  AMC:
    admission grammar machine-closed;

  OCTT:
    evidence grammar machine-closed;

  Public translation:
    NOT YET ADJUDICABLE because empirical/domain entry remains open.

No empirical result is manufactured.
-/
theorem life_origin_companion_machine_checkpoint :
    PlusThree.SieveComplete
      (LifeChemistry.lifeWorld () ())
    ∧ OriginOfLifeAMC.AMCPositive
        OriginOfLifeAMC.positiveDemo
    ∧ OriginOfLifeAMC.AMCNegative
        OriginOfLifeAMC.negativeDemo
    ∧ OriginOfLifeAMC.AMCIndeterminate
        OriginOfLifeAMC.indeterminateDemo
    ∧ OriginOfLifeOCTT.CarrierContinuityPositive
        OriginOfLifeOCTT.carrierPositiveDemo
    ∧ OriginOfLifeOCTT.LineageContinuityPositive
        OriginOfLifeOCTT.lineagePositiveDemo
    ∧ OriginOfLifeOCTT.OCTTIndeterminate
        OriginOfLifeOCTT.indeterminateDemo
    ∧ UniversalTranslationContract.NotYetAdjudicable
        lifeOriginPublicWorld := by
  exact
    ⟨LifeChemistry.life_sieve_complete () (),
     OriginOfLifeAMC.positive_demo_is_positive,
     OriginOfLifeAMC.negative_demo_is_negative,
     OriginOfLifeAMC.indeterminate_demo_is_indeterminate,
     OriginOfLifeOCTT.carrier_positive_demo,
     OriginOfLifeOCTT.lineage_positive_demo,
     OriginOfLifeOCTT.octt_indeterminate_demo,
     life_origin_public_kernel_not_yet_adjudicable⟩

/-!
Machine-facing compression
--------------------------
SCOPED SF LIFE OBJECT: CONFIRMED
+
AMC ADMISSION CONTRACT: MACHINE-CLOSED AS PROCEDURE
+
OCTT EVIDENCE CONTRACT: MACHINE-CLOSED AS PROCEDURE
+
REAL EMPIRICAL AMC ENTRY: OPEN
+
TARGET CARRIER / LEVEL / SCOPE / STRUCTURAL PRESERVATION: OPEN
=
PUBLIC UNIVERSAL TRANSLATION CONTRACT:
NOT YET ADJUDICABLE

The Universal Kernel remains unchanged.
-/

end LifeOriginPublicKernelAdapter
end StructuralFlow

/-!
===============================================================================
PUBLISHED-SYSTEM INSTANCE SEATS v0.1
===============================================================================

ROLE
----
Conservative literature-status instances for:

  * Hardy et al. 2015 catalytic membrane system;
  * Matsuo et al. 2019 monocomponent self-reproducing liposome.

These seats encode only what the reviewed publications support strongly enough
for the current AMC / OCTT contracts.

They do NOT encode:

  * new experimental execution;
  * author correspondence;
  * unreported negative results;
  * empirical AMC POSITIVE;
  * empirical OCTT carrier-continuity POSITIVE;
  * Life.

OPEN means:
the present public evidence reviewed for this project does not yet discharge
the burden at the declared carrier-level AMC/OCTT scope.

No OPEN burden is converted into a VIOLATION.
===============================================================================
-/

namespace StructuralFlow
namespace LifeOriginPublishedInstances

open OriginOfLifeAMC
open OriginOfLifeOCTT
open LifeOriginPublicKernelAdapter
open UniversalTranslationContract

/-! --------------------------------------------------------------------------
Published-system pin vocabulary
---------------------------------------------------------------------------- -/

inductive PublishedSystem where
  | hardy2015
  | matsuo2019
deriving DecidableEq, Repr

inductive PublishedEnvironment where
  | reportedExperimentalConditions
deriving DecidableEq, Repr

inductive PublishedLevel where
  | catalyticMembraneCarrier
deriving DecidableEq, Repr

inductive PublishedScope where
  | boundedCarrierAMC
deriving DecidableEq, Repr

inductive PublishedHorizon where
  | reportedObservationWindow
deriving DecidableEq, Repr

inductive PublishedBoundary where
  | vesicleMembrane
deriving DecidableEq, Repr

inductive PublishedProcess where
  | catalystGeneration
  | membraneLipidGeneration
  | membraneGrowth
  | buddingDivision
  | deNovoNucleation
deriving DecidableEq, Repr

inductive PublishedControl where
  | membraneEmbeddedCatalyst
  | membraneSurface
deriving DecidableEq, Repr

def hardyPins :
    OriginOfLifeAMC.Pins
      PublishedSystem
      PublishedEnvironment
      PublishedLevel
      PublishedScope
      PublishedHorizon
      PublishedBoundary
      PublishedProcess
      PublishedControl
    where
  system := PublishedSystem.hardy2015
  environment := PublishedEnvironment.reportedExperimentalConditions
  level := PublishedLevel.catalyticMembraneCarrier
  scope := PublishedScope.boundedCarrierAMC
  horizon := PublishedHorizon.reportedObservationWindow
  boundary := PublishedBoundary.vesicleMembrane
  processes := fun p =>
    p = PublishedProcess.catalystGeneration
    ∨ p = PublishedProcess.membraneLipidGeneration
    ∨ p = PublishedProcess.membraneGrowth
    ∨ p = PublishedProcess.buddingDivision
    ∨ p = PublishedProcess.deNovoNucleation
  controls := fun c =>
    c = PublishedControl.membraneEmbeddedCatalyst
    ∨ c = PublishedControl.membraneSurface

def matsuoPins :
    OriginOfLifeAMC.Pins
      PublishedSystem
      PublishedEnvironment
      PublishedLevel
      PublishedScope
      PublishedHorizon
      PublishedBoundary
      PublishedProcess
      PublishedControl
    where
  system := PublishedSystem.matsuo2019
  environment := PublishedEnvironment.reportedExperimentalConditions
  level := PublishedLevel.catalyticMembraneCarrier
  scope := PublishedScope.boundedCarrierAMC
  horizon := PublishedHorizon.reportedObservationWindow
  boundary := PublishedBoundary.vesicleMembrane
  processes := fun p =>
    p = PublishedProcess.membraneLipidGeneration
    ∨ p = PublishedProcess.membraneGrowth
    ∨ p = PublishedProcess.buddingDivision
  controls := fun c =>
    c = PublishedControl.membraneSurface

/-! --------------------------------------------------------------------------
Hardy 2015 — AMC literature state
---------------------------------------------------------------------------- -/

/-
Current literature-grounded AMC reading:

AMC-0 PINS:
  discharged at the published-system level.

AMC-1 CONTROL EFFICACY:
  discharged for TLTA-mediated catalyst / phospholipid production.

AMC-2 ENDOGENEITY:
  discharged at the selected catalyst+membrane subsystem level:
  the reported system generates additional catalyst ligand and membrane lipid
  from supplied precursors.

AMC-3 MUTUAL INTEGRATION:
  discharged for the selected subsystem:
  membrane-localized catalyst generates catalyst + membrane material, while the
  membrane environment materially supports the catalytic chemistry.

AMC-4 REGENERATION:
  discharged:
  repeated catalyst and phospholipid generation is directly reported.

AMC-5 CONTINUED ORGANIZATIONAL COMPETENCE:
  OPEN at the bounded-carrier OCTT scope:
  long-run population propagation is strong, but deep carrier-resolved turnover
  is not yet discharged.

AMC-6 ASSAY ADEQUACY:
  OPEN for the full bounded-carrier AMC claim:
  the published work did not perform the source-resolved OCTT now required by
  this project.
-/
def hardyAMCState :
    OriginOfLifeAMC.Burden -> OriginOfLifeAMC.EvidenceState
  | .pins => .discharged
  | .controlEfficacy => .discharged
  | .endogeneity => .discharged
  | .mutualIntegration => .discharged
  | .regeneration => .discharged
  | .continuedOrganizationalCompetence => .open
  | .assayAdequacy => .open

def publishedAMCEvidence :
    OriginOfLifeAMC.Burden ->
    OriginOfLifeAMC.EvidenceState ->
    Prop :=
  fun _ _ => True

def hardyAMCWorld :
    OriginOfLifeAMC.World
      PublishedSystem
      PublishedEnvironment
      PublishedLevel
      PublishedScope
      PublishedHorizon
      PublishedBoundary
      PublishedProcess
      PublishedControl
    where
  pins := hardyPins
  state := hardyAMCState
  evidence := publishedAMCEvidence
  warrant := by
    intro b
    simp [publishedAMCEvidence]

theorem hardy_amc_not_positive :
    ¬ OriginOfLifeAMC.AMCPositive hardyAMCWorld := by
  apply OriginOfLifeAMC.assay_not_discharged_blocks_positive
  simp [hardyAMCWorld, hardyAMCState]

theorem hardy_amc_not_negative :
    ¬ OriginOfLifeAMC.AMCNegative hardyAMCWorld := by
  intro hNeg
  rcases hNeg with
    ⟨_hPins, _hAssay, b, hSubstantive, hViolated⟩
  cases b <;>
    simp [OriginOfLifeAMC.SubstantiveBurden,
          hardyAMCWorld,
          hardyAMCState] at hSubstantive hViolated

theorem hardy_amc_indeterminate :
    OriginOfLifeAMC.AMCIndeterminate hardyAMCWorld := by
  exact
    ⟨hardy_amc_not_positive,
     hardy_amc_not_negative⟩

/-! --------------------------------------------------------------------------
Hardy 2015 — OCTT literature state
---------------------------------------------------------------------------- -/

/-
Published Hardy evidence already supports:

  * repeated population-level catalyst / membrane synthesis;
  * strong seed dilution by serial transfer;
  * observed division-like events;
  * observed de novo nucleation as a competing pathway.

The exact OCTT burden remains OPEN because the same carrier / explicit daughter
lineage has not yet been source-resolved through deep load-bearing turnover.
-/
def hardyOCTTState :
    OriginOfLifeOCTT.Burden -> OriginOfLifeAMC.EvidenceState
  | .sourceAgeResolution => .open
  | .carrierAncestryResolution => .open
  | .passiveSeedExclusion => .open
  | .maintenanceFunction => .discharged
  | .assayAdequacy => .open

def publishedOCTTEvidence :
    OriginOfLifeOCTT.Burden ->
    OriginOfLifeAMC.EvidenceState ->
    Prop :=
  fun _ _ => True

def hardyOCTTWorld :
    OriginOfLifeOCTT.World where
  state := hardyOCTTState
  evidence := publishedOCTTEvidence
  warrant := by
    intro b
    simp [publishedOCTTEvidence]
  continuity := OriginOfLifeOCTT.ContinuityClass.indeterminate

theorem hardy_octt_indeterminate :
    OriginOfLifeOCTT.OCTTIndeterminate hardyOCTTWorld := by
  exact
    Or.inl
      ⟨OriginOfLifeOCTT.Burden.sourceAgeResolution,
       by
         simp [hardyOCTTWorld, hardyOCTTState]⟩

/-! --------------------------------------------------------------------------
Matsuo 2019 — AMC literature state
---------------------------------------------------------------------------- -/

/-
Current literature-grounded AMC reading:

AMC-0 PINS:
  discharged at the published-system level.

AMC-1 CONTROL EFFICACY:
  discharged:
  the pre-existing membrane surface promotes formation of additional membrane
  lipid from precursor under the reported phosphate-buffer conditions.

AMC-2 ENDOGENEITY:
  discharged at the selected membrane-production scope:
  the candidate carrier contributes the catalytic surface required for new
  membrane-lipid formation.

AMC-3 MUTUAL INTEGRATION:
  OPEN:
  this is deliberately the adversarial one-control case.  The current AMC
  contract must not assume that one self-catalytic boundary is either sufficient
  or insufficient before OCTT / comparative adjudication.

AMC-4 REGENERATION:
  discharged for membrane material generation.

AMC-5 CONTINUED ORGANIZATIONAL COMPETENCE:
  OPEN at the source-resolved bounded-carrier turnover scope.

AMC-6 ASSAY ADEQUACY:
  OPEN for the full AMC claim.
-/
def matsuoAMCState :
    OriginOfLifeAMC.Burden -> OriginOfLifeAMC.EvidenceState
  | .pins => .discharged
  | .controlEfficacy => .discharged
  | .endogeneity => .discharged
  | .mutualIntegration => .open
  | .regeneration => .discharged
  | .continuedOrganizationalCompetence => .open
  | .assayAdequacy => .open

def matsuoAMCWorld :
    OriginOfLifeAMC.World
      PublishedSystem
      PublishedEnvironment
      PublishedLevel
      PublishedScope
      PublishedHorizon
      PublishedBoundary
      PublishedProcess
      PublishedControl
    where
  pins := matsuoPins
  state := matsuoAMCState
  evidence := publishedAMCEvidence
  warrant := by
    intro b
    simp [publishedAMCEvidence]

theorem matsuo_amc_not_positive :
    ¬ OriginOfLifeAMC.AMCPositive matsuoAMCWorld := by
  apply OriginOfLifeAMC.assay_not_discharged_blocks_positive
  simp [matsuoAMCWorld, matsuoAMCState]

theorem matsuo_amc_not_negative :
    ¬ OriginOfLifeAMC.AMCNegative matsuoAMCWorld := by
  intro hNeg
  rcases hNeg with
    ⟨_hPins, _hAssay, b, hSubstantive, hViolated⟩
  cases b <;>
    simp [OriginOfLifeAMC.SubstantiveBurden,
          matsuoAMCWorld,
          matsuoAMCState] at hSubstantive hViolated

theorem matsuo_amc_indeterminate :
    OriginOfLifeAMC.AMCIndeterminate matsuoAMCWorld := by
  exact
    ⟨matsuo_amc_not_positive,
     matsuo_amc_not_negative⟩

/-! --------------------------------------------------------------------------
Matsuo 2019 — OCTT literature state
---------------------------------------------------------------------------- -/

/-
Published Matsuo evidence supports autocatalytic membrane-lipid formation and
budding / division.

The project-level OCTT burden remains OPEN because the reviewed publication does
not source-resolve initial versus newly generated load-bearing membrane material
through an explicitly adjudicated carrier lineage across the required turnover
horizon.
-/
def matsuoOCTTState :
    OriginOfLifeOCTT.Burden -> OriginOfLifeAMC.EvidenceState
  | .sourceAgeResolution => .open
  | .carrierAncestryResolution => .open
  | .passiveSeedExclusion => .open
  | .maintenanceFunction => .discharged
  | .assayAdequacy => .open

def matsuoOCTTWorld :
    OriginOfLifeOCTT.World where
  state := matsuoOCTTState
  evidence := publishedOCTTEvidence
  warrant := by
    intro b
    simp [publishedOCTTEvidence]
  continuity := OriginOfLifeOCTT.ContinuityClass.indeterminate

theorem matsuo_octt_indeterminate :
    OriginOfLifeOCTT.OCTTIndeterminate matsuoOCTTWorld := by
  exact
    Or.inl
      ⟨OriginOfLifeOCTT.Burden.sourceAgeResolution,
       by
         simp [matsuoOCTTWorld, matsuoOCTTState]⟩

/-! --------------------------------------------------------------------------
Comparative instance firewalls
---------------------------------------------------------------------------- -/

/--
The current publications do not close either candidate as AMC POSITIVE under the
new contract.
-/
theorem published_candidates_remain_amc_open :
    OriginOfLifeAMC.AMCIndeterminate hardyAMCWorld
    ∧ OriginOfLifeAMC.AMCIndeterminate matsuoAMCWorld := by
  exact
    ⟨hardy_amc_indeterminate,
     matsuo_amc_indeterminate⟩

/--
The current publications do not close OCTT at the source-resolved
carrier-turnover level for either candidate.
-/
theorem published_candidates_remain_octt_open :
    OriginOfLifeOCTT.OCTTIndeterminate hardyOCTTWorld
    ∧ OriginOfLifeOCTT.OCTTIndeterminate matsuoOCTTWorld := by
  exact
    ⟨hardy_octt_indeterminate,
     matsuo_octt_indeterminate⟩

/--
Published candidate mapping does not discharge the public-kernel empirical AMC
entry.  The adapter therefore remains NOT YET ADJUDICABLE.
-/
theorem published_instances_do_not_close_public_translation :
    OriginOfLifeAMC.AMCIndeterminate hardyAMCWorld
    ∧ OriginOfLifeAMC.AMCIndeterminate matsuoAMCWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨hardy_amc_indeterminate,
     matsuo_amc_indeterminate,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

/-! --------------------------------------------------------------------------
v0.2 combined machine checkpoint
---------------------------------------------------------------------------- -/

theorem life_origin_companion_v0_2_machine_checkpoint :
    LifeChemistry.ChemicalActivity LifeChemistry.LifeCase.failure
    ∧ OriginOfLifeAMC.AMCIndeterminate hardyAMCWorld
    ∧ OriginOfLifeOCTT.OCTTIndeterminate hardyOCTTWorld
    ∧ OriginOfLifeAMC.AMCIndeterminate matsuoAMCWorld
    ∧ OriginOfLifeOCTT.OCTTIndeterminate matsuoOCTTWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨LifeChemistry.activity_survives_selected_life_failure,
     hardy_amc_indeterminate,
     hardy_octt_indeterminate,
     matsuo_amc_indeterminate,
     matsuo_octt_indeterminate,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

/-!
Machine-facing compression
--------------------------
HARDY 2015:
  AMC INDETERMINATE
  OCTT INDETERMINATE

MATSUO 2019:
  AMC INDETERMINATE
  OCTT INDETERMINATE

NO CURRENT PUBLISHED INSTANCE:
  discharges empirical AMC entry.

PUBLIC UNIVERSAL TRANSLATION:
  remains NOT YET ADJUDICABLE.

The Universal Kernel remains unchanged.
-/

end LifeOriginPublishedInstances
end StructuralFlow

/-!
===============================================================================
PROSPECTIVE HARDY OCTT / AMC EXPERIMENT CONTRACT v0.1
===============================================================================

ROLE
----
Machine-close the proposed Hardy experiment as an adjudication procedure
BEFORE experimental execution.

This seat does NOT claim that any prospective result has occurred.

It encodes lawful result branches:

  H-C1  continuous bounded carry through turnover;
  H-C2  daughter-lineage carry through turnover;
  H-C3  de novo new-carrier production;
  H-C5  population propagation only;
  H-I   indeterminate / insufficient evidence.

It then shows how those branches constrain the AMC and public-translation seats.

Critical firewalls:

  * C1 / C2 do not become AMC POSITIVE merely because OCTT is positive.
    AMC becomes positive only in the separately constructed prospective branch
    where ALL AMC burdens are also discharged.

  * C3 / C5 do not become carrier-level AMC positives.

  * a prospective StructuralConforms world is a CONDITIONAL ENDPOINT MODEL.
    It is not the current evidence state.

  * the current real public adapter remains NOT YET ADJUDICABLE.
===============================================================================
-/

namespace StructuralFlow
namespace LifeOriginProspectiveHardy

open OriginOfLifeAMC
open OriginOfLifeOCTT
open LifeOriginPublicKernelAdapter
open LifeOriginPublishedInstances
open UniversalTranslationContract

/-! --------------------------------------------------------------------------
Prospective OCTT evidence state
---------------------------------------------------------------------------- -/

/--
A fully executed / adequate OCTT branch has all OCTT burdens discharged.

The continuity class then determines what kind of result was obtained.
-/
def hardyExecutedOCTTState :
    OriginOfLifeOCTT.Burden -> OriginOfLifeAMC.EvidenceState :=
  fun _ => OriginOfLifeAMC.EvidenceState.discharged

def prospectiveOCTTEvidence :
    OriginOfLifeOCTT.Burden ->
    OriginOfLifeAMC.EvidenceState ->
    Prop :=
  fun _ _ => True

def hardyC1World :
    OriginOfLifeOCTT.World where
  state := hardyExecutedOCTTState
  evidence := prospectiveOCTTEvidence
  warrant := by
    intro b
    simp [prospectiveOCTTEvidence]
  continuity :=
    OriginOfLifeOCTT.ContinuityClass.continuousBoundedCarry

def hardyC2World :
    OriginOfLifeOCTT.World where
  state := hardyExecutedOCTTState
  evidence := prospectiveOCTTEvidence
  warrant := by
    intro b
    simp [prospectiveOCTTEvidence]
  continuity :=
    OriginOfLifeOCTT.ContinuityClass.daughterLineageCarry

def hardyC3World :
    OriginOfLifeOCTT.World where
  state := hardyExecutedOCTTState
  evidence := prospectiveOCTTEvidence
  warrant := by
    intro b
    simp [prospectiveOCTTEvidence]
  continuity :=
    OriginOfLifeOCTT.ContinuityClass.deNovoNucleation

def hardyC5World :
    OriginOfLifeOCTT.World where
  state := hardyExecutedOCTTState
  evidence := prospectiveOCTTEvidence
  warrant := by
    intro b
    simp [prospectiveOCTTEvidence]
  continuity :=
    OriginOfLifeOCTT.ContinuityClass.populationPropagation

def hardyIndeterminateState :
    OriginOfLifeOCTT.Burden -> OriginOfLifeAMC.EvidenceState
  | .sourceAgeResolution => .open
  | _ => .discharged

def hardyIndeterminateWorld :
    OriginOfLifeOCTT.World where
  state := hardyIndeterminateState
  evidence := prospectiveOCTTEvidence
  warrant := by
    intro b
    simp [prospectiveOCTTEvidence]
  continuity :=
    OriginOfLifeOCTT.ContinuityClass.indeterminate

/-! --------------------------------------------------------------------------
Prospective OCTT branch theorems
---------------------------------------------------------------------------- -/

theorem hardy_c1_branch :
    OriginOfLifeOCTT.CarrierContinuityPositive
      hardyC1World := by
  constructor
  · intro b
    rfl
  · rfl

theorem hardy_c2_branch :
    OriginOfLifeOCTT.LineageContinuityPositive
      hardyC2World := by
  constructor
  · intro b
    rfl
  · rfl

theorem hardy_c3_branch :
    OriginOfLifeOCTT.NewCarrierProduction
      hardyC3World := by
  constructor
  · intro b
    rfl
  · rfl

theorem hardy_c5_branch :
    OriginOfLifeOCTT.PopulationPropagation
      hardyC5World := by
  constructor
  · intro b
    rfl
  · rfl

theorem hardy_indeterminate_branch :
    OriginOfLifeOCTT.OCTTIndeterminate
      hardyIndeterminateWorld := by
  exact
    Or.inl
      ⟨OriginOfLifeOCTT.Burden.sourceAgeResolution,
       by
         simp [hardyIndeterminateWorld, hardyIndeterminateState]⟩

/-! --------------------------------------------------------------------------
Prospective Hardy AMC branches
---------------------------------------------------------------------------- -/

/--
Strong-success AMC branch.

This world is NOT the current Hardy literature state.

It represents the future branch in which:
  * the already-supported Hardy AMC-0 ... AMC-4 burdens remain discharged; and
  * the proposed experiment additionally discharges AMC-5 continued
    organizational competence and AMC-6 assay adequacy.

Only that complete branch earns AMC POSITIVE.
-/
def hardyCarrierSuccessAMCState :
    OriginOfLifeAMC.Burden -> OriginOfLifeAMC.EvidenceState :=
  fun _ => OriginOfLifeAMC.EvidenceState.discharged

def hardyCarrierSuccessAMCWorld :
    OriginOfLifeAMC.World
      LifeOriginPublishedInstances.PublishedSystem
      LifeOriginPublishedInstances.PublishedEnvironment
      LifeOriginPublishedInstances.PublishedLevel
      LifeOriginPublishedInstances.PublishedScope
      LifeOriginPublishedInstances.PublishedHorizon
      LifeOriginPublishedInstances.PublishedBoundary
      LifeOriginPublishedInstances.PublishedProcess
      LifeOriginPublishedInstances.PublishedControl
    where
  pins := LifeOriginPublishedInstances.hardyPins
  state := hardyCarrierSuccessAMCState
  evidence := LifeOriginPublishedInstances.publishedAMCEvidence
  warrant := by
    intro b
    simp [LifeOriginPublishedInstances.publishedAMCEvidence]

theorem hardy_success_branch_amc_positive :
    OriginOfLifeAMC.AMCPositive
      hardyCarrierSuccessAMCWorld := by
  intro b
  rfl

/--
C3 / C5 conservative AMC branch.

Even with an adequate OCTT assay, de novo new-carrier production or
population-only propagation does not by itself discharge bounded-carrier
continued organizational competence.

Therefore AMC-5 remains OPEN.
-/
def hardyNonCarrierAMCState :
    OriginOfLifeAMC.Burden -> OriginOfLifeAMC.EvidenceState
  | .continuedOrganizationalCompetence => .open
  | _ => .discharged

def hardyNonCarrierAMCWorld :
    OriginOfLifeAMC.World
      LifeOriginPublishedInstances.PublishedSystem
      LifeOriginPublishedInstances.PublishedEnvironment
      LifeOriginPublishedInstances.PublishedLevel
      LifeOriginPublishedInstances.PublishedScope
      LifeOriginPublishedInstances.PublishedHorizon
      LifeOriginPublishedInstances.PublishedBoundary
      LifeOriginPublishedInstances.PublishedProcess
      LifeOriginPublishedInstances.PublishedControl
    where
  pins := LifeOriginPublishedInstances.hardyPins
  state := hardyNonCarrierAMCState
  evidence := LifeOriginPublishedInstances.publishedAMCEvidence
  warrant := by
    intro b
    simp [LifeOriginPublishedInstances.publishedAMCEvidence]

theorem hardy_noncarrier_amc_not_positive :
    ¬ OriginOfLifeAMC.AMCPositive
        hardyNonCarrierAMCWorld := by
  intro hPos
  have h :=
    hPos
      OriginOfLifeAMC.Burden.continuedOrganizationalCompetence
  simp [hardyNonCarrierAMCWorld, hardyNonCarrierAMCState] at h

theorem hardy_noncarrier_amc_not_negative :
    ¬ OriginOfLifeAMC.AMCNegative
        hardyNonCarrierAMCWorld := by
  intro hNeg
  rcases hNeg with
    ⟨_hPins, _hAssay, b, hSubstantive, hViolated⟩
  cases b <;>
    simp [OriginOfLifeAMC.SubstantiveBurden,
          hardyNonCarrierAMCWorld,
          hardyNonCarrierAMCState] at hSubstantive hViolated

theorem hardy_noncarrier_amc_indeterminate :
    OriginOfLifeAMC.AMCIndeterminate
      hardyNonCarrierAMCWorld := by
  exact
    ⟨hardy_noncarrier_amc_not_positive,
     hardy_noncarrier_amc_not_negative⟩

/-! --------------------------------------------------------------------------
OCTT -> AMC branch discipline
---------------------------------------------------------------------------- -/

/--
C1 plus independently discharged AMC burdens supports the positive AMC branch.

The conjunction is explicit:
OCTT does not logically imply AMC by itself.
-/
theorem hardy_c1_plus_full_amc_branch :
    OriginOfLifeOCTT.CarrierContinuityPositive
      hardyC1World
    ∧ OriginOfLifeAMC.AMCPositive
        hardyCarrierSuccessAMCWorld := by
  exact
    ⟨hardy_c1_branch,
     hardy_success_branch_amc_positive⟩

/--
C2 plus independently discharged AMC burdens supports the positive AMC branch.
-/
theorem hardy_c2_plus_full_amc_branch :
    OriginOfLifeOCTT.LineageContinuityPositive
      hardyC2World
    ∧ OriginOfLifeAMC.AMCPositive
        hardyCarrierSuccessAMCWorld := by
  exact
    ⟨hardy_c2_branch,
     hardy_success_branch_amc_positive⟩

/--
C3 is lawful new-carrier production but does not close bounded-carrier AMC.
-/
theorem hardy_c3_keeps_carrier_amc_open :
    OriginOfLifeOCTT.NewCarrierProduction
      hardyC3World
    ∧ OriginOfLifeAMC.AMCIndeterminate
        hardyNonCarrierAMCWorld := by
  exact
    ⟨hardy_c3_branch,
     hardy_noncarrier_amc_indeterminate⟩

/--
C5 is lawful population propagation but does not close bounded-carrier AMC.
-/
theorem hardy_c5_keeps_carrier_amc_open :
    OriginOfLifeOCTT.PopulationPropagation
      hardyC5World
    ∧ OriginOfLifeAMC.AMCIndeterminate
        hardyNonCarrierAMCWorld := by
  exact
    ⟨hardy_c5_branch,
     hardy_noncarrier_amc_indeterminate⟩

/-! --------------------------------------------------------------------------
Prospective AMC -> scoped SF Life public translation endpoint
---------------------------------------------------------------------------- -/

/-
This world is a CONDITIONAL ENDPOINT MODEL.

It represents the future branch in which:
  * the origin-of-life surface is warranted;
  * one real carrier is pinned;
  * object / level / scope are pinned;
  * structural preservation is discharged;
  * non-circularity and identity firewall remain discharged;
  * all Life-specific object burdens are discharged;
  * empirical AMC admission is discharged.

It is NOT the current public adapter world.
-/

def prospectiveCoreState :
    UniversalTranslationContract.CoreBurden ->
    UniversalTranslationContract.Disposition :=
  fun _ => UniversalTranslationContract.Disposition.discharged

def prospectiveObjectState :
    LifeOriginPublicKernelAdapter.ObjectBurden ->
    UniversalTranslationContract.Disposition :=
  fun _ => UniversalTranslationContract.Disposition.discharged

def prospectiveDomainState :
    LifeOriginPublicKernelAdapter.DomainBurden ->
    UniversalTranslationContract.Disposition :=
  fun _ => UniversalTranslationContract.Disposition.discharged

noncomputable def hardyProspectiveConformingWorld :
    UniversalTranslationContract.World
      LifeOriginPublicKernelAdapter.ObjectBurden
      LifeOriginPublicKernelAdapter.DomainBurden
    where

  coreState := prospectiveCoreState
  coreEvidence := fun b state =>
    state = prospectiveCoreState b
  coreWarrant := by
    intro b
    rfl

  objectRequired :=
    LifeOriginPublicKernelAdapter.objectRequired
  objectState := prospectiveObjectState
  objectEvidence := fun b state =>
    state = prospectiveObjectState b
  objectWarrant := by
    intro b _hRequired
    rfl

  domainEntryRequired :=
    LifeOriginPublicKernelAdapter.domainEntryRequired
  domainDownstreamRequired :=
    LifeOriginPublicKernelAdapter.domainDownstreamRequired
  domainRoleDisjoint :=
    LifeOriginPublicKernelAdapter.lifeOriginPublicWorld.domainRoleDisjoint

  domainState := prospectiveDomainState
  domainEvidence := fun b state =>
    state = prospectiveDomainState b
  domainWarrant := by
    intro b _hRequired
    rfl

theorem hardy_prospective_translation_structural_conforms :
    UniversalTranslationContract.StructuralConforms
      hardyProspectiveConformingWorld := by
  simp [UniversalTranslationContract.StructuralConforms,
        UniversalTranslationContract.GatingPass,
        hardyProspectiveConformingWorld,
        prospectiveCoreState,
        prospectiveObjectState,
        prospectiveDomainState,
        LifeOriginPublicKernelAdapter.objectRequired,
        LifeOriginPublicKernelAdapter.domainEntryRequired]

/-! --------------------------------------------------------------------------
Current world remains open
---------------------------------------------------------------------------- -/

/--
The prospective endpoint does not mutate the current evidence state.
-/
theorem current_public_adapter_remains_not_yet_adjudicable :
    UniversalTranslationContract.NotYetAdjudicable
      LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable

/-! --------------------------------------------------------------------------
Full prospective endpoint branches
---------------------------------------------------------------------------- -/

/--
Strong C1 branch:

If the experiment actually earns the C1 OCTT world,
AND independently earns the full AMC-positive world,
AND independently discharges every public translation burden,
then the encoded endpoint structurally conforms.

This theorem machine-closes the adjudication branch.
It does not assert that the branch has occurred.
-/
theorem hardy_c1_full_contract_endpoint :
    OriginOfLifeOCTT.CarrierContinuityPositive hardyC1World
    ∧ OriginOfLifeAMC.AMCPositive hardyCarrierSuccessAMCWorld
    ∧ UniversalTranslationContract.StructuralConforms
        hardyProspectiveConformingWorld := by
  exact
    ⟨hardy_c1_branch,
     hardy_success_branch_amc_positive,
     hardy_prospective_translation_structural_conforms⟩

/--
Strong C2 branch:

Lineage continuity can also reach the prospective structural-conformance
endpoint if the separately required AMC and translation burdens are discharged.

No parent = daughter strict-identity claim is made.
-/
theorem hardy_c2_full_contract_endpoint :
    OriginOfLifeOCTT.LineageContinuityPositive hardyC2World
    ∧ OriginOfLifeAMC.AMCPositive hardyCarrierSuccessAMCWorld
    ∧ UniversalTranslationContract.StructuralConforms
        hardyProspectiveConformingWorld := by
  exact
    ⟨hardy_c2_branch,
     hardy_success_branch_amc_positive,
     hardy_prospective_translation_structural_conforms⟩

/--
C3 cannot use the prospective strong endpoint merely because the assay was
fully executed.

The branch remains:
  new-carrier production + bounded-carrier AMC indeterminate.
-/
theorem hardy_c3_contract_endpoint :
    OriginOfLifeOCTT.NewCarrierProduction hardyC3World
    ∧ OriginOfLifeAMC.AMCIndeterminate hardyNonCarrierAMCWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨hardy_c3_branch,
     hardy_noncarrier_amc_indeterminate,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

/--
C5 cannot use the prospective strong endpoint merely because population
turnover was demonstrated.

The branch remains:
  population propagation + bounded-carrier AMC indeterminate.
-/
theorem hardy_c5_contract_endpoint :
    OriginOfLifeOCTT.PopulationPropagation hardyC5World
    ∧ OriginOfLifeAMC.AMCIndeterminate hardyNonCarrierAMCWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨hardy_c5_branch,
     hardy_noncarrier_amc_indeterminate,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

/-! --------------------------------------------------------------------------
Prospective contract machine checkpoint
---------------------------------------------------------------------------- -/

theorem hardy_prospective_experiment_contract_machine_checkpoint :
    OriginOfLifeOCTT.CarrierContinuityPositive hardyC1World
    ∧ OriginOfLifeOCTT.LineageContinuityPositive hardyC2World
    ∧ OriginOfLifeOCTT.NewCarrierProduction hardyC3World
    ∧ OriginOfLifeOCTT.PopulationPropagation hardyC5World
    ∧ OriginOfLifeOCTT.OCTTIndeterminate hardyIndeterminateWorld
    ∧ OriginOfLifeAMC.AMCPositive hardyCarrierSuccessAMCWorld
    ∧ OriginOfLifeAMC.AMCIndeterminate hardyNonCarrierAMCWorld
    ∧ UniversalTranslationContract.StructuralConforms
        hardyProspectiveConformingWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨hardy_c1_branch,
     hardy_c2_branch,
     hardy_c3_branch,
     hardy_c5_branch,
     hardy_indeterminate_branch,
     hardy_success_branch_amc_positive,
     hardy_noncarrier_amc_indeterminate,
     hardy_prospective_translation_structural_conforms,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

/-!
Machine-facing compression
--------------------------

CURRENT REAL STATE:
  Hardy literature AMC       = INDETERMINATE
  Hardy literature OCTT      = INDETERMINATE
  public AMC -> Life adapter = NOT YET ADJUDICABLE

PROSPECTIVE EXECUTED RESULT BRANCHES:

  C1 + full AMC + full translation burdens
    -> STRUCTURAL CONFORMS

  C2 + full AMC + full translation burdens
    -> STRUCTURAL CONFORMS

  C3
    -> NEW-CARRIER PRODUCTION
    -> bounded-carrier AMC remains INDETERMINATE

  C5
    -> POPULATION PROPAGATION
    -> bounded-carrier AMC remains INDETERMINATE

  insufficient source / ancestry / passive-seed evidence
    -> OCTT INDETERMINATE

The Universal Kernel remains unchanged.
No prospective branch is asserted as empirical fact.
-/

end LifeOriginProspectiveHardy
end StructuralFlow

/-!
===============================================================================
PROSPECTIVE MATSUO ADVERSARIAL CONTRACT v0.1
===============================================================================

ROLE
----
Machine-close the Matsuo one-control adversarial branches before execution.

Scientific purpose:

Matsuo 2019 is not a weaker copy of the Hardy arm.

It pressures a different hypothesis:

  DOES A SINGLE SELF-CATALYTIC MEMBRANE CONTROL ALREADY SATISFY THE
  AUTONOMOUS-MAINTENANCE BURDENS IF SOURCE-RESOLVED CARRIER TURNOVER IS SHOWN?

The current AMC contract does NOT encode:

  "multiple differentiated controls are required."

Therefore the machine must permit two lawful future outcomes:

A. OCTT succeeds but AMC-3 MUTUAL INTEGRATION remains OPEN
   -> AMC remains INDETERMINATE.

B. OCTT succeeds and the one-control architecture independently discharges
   AMC-3 as well as every other AMC burden
   -> AMC POSITIVE is lawful.

If B occurs experimentally, any separate hypothesis that differentiated
multiple controls are necessary for AMC loses support.

No branch below is asserted as empirical fact.
===============================================================================
-/

namespace StructuralFlow
namespace LifeOriginProspectiveMatsuo

open OriginOfLifeAMC
open OriginOfLifeOCTT
open LifeOriginPublicKernelAdapter
open LifeOriginPublishedInstances
open UniversalTranslationContract

/-! --------------------------------------------------------------------------
Prospective Matsuo OCTT result worlds
---------------------------------------------------------------------------- -/

def matsuoExecutedOCTTState :
    OriginOfLifeOCTT.Burden -> OriginOfLifeAMC.EvidenceState :=
  fun _ => OriginOfLifeAMC.EvidenceState.discharged

def matsuoProspectiveOCTTEvidence :
    OriginOfLifeOCTT.Burden ->
    OriginOfLifeAMC.EvidenceState ->
    Prop :=
  fun _ _ => True

def matsuoC1World :
    OriginOfLifeOCTT.World where
  state := matsuoExecutedOCTTState
  evidence := matsuoProspectiveOCTTEvidence
  warrant := by
    intro b
    simp [matsuoProspectiveOCTTEvidence]
  continuity :=
    OriginOfLifeOCTT.ContinuityClass.continuousBoundedCarry

def matsuoC2World :
    OriginOfLifeOCTT.World where
  state := matsuoExecutedOCTTState
  evidence := matsuoProspectiveOCTTEvidence
  warrant := by
    intro b
    simp [matsuoProspectiveOCTTEvidence]
  continuity :=
    OriginOfLifeOCTT.ContinuityClass.daughterLineageCarry

def matsuoC3World :
    OriginOfLifeOCTT.World where
  state := matsuoExecutedOCTTState
  evidence := matsuoProspectiveOCTTEvidence
  warrant := by
    intro b
    simp [matsuoProspectiveOCTTEvidence]
  continuity :=
    OriginOfLifeOCTT.ContinuityClass.deNovoNucleation

def matsuoC5World :
    OriginOfLifeOCTT.World where
  state := matsuoExecutedOCTTState
  evidence := matsuoProspectiveOCTTEvidence
  warrant := by
    intro b
    simp [matsuoProspectiveOCTTEvidence]
  continuity :=
    OriginOfLifeOCTT.ContinuityClass.populationPropagation

def matsuoIndeterminateState :
    OriginOfLifeOCTT.Burden -> OriginOfLifeAMC.EvidenceState
  | .sourceAgeResolution => .open
  | _ => .discharged

def matsuoIndeterminateWorld :
    OriginOfLifeOCTT.World where
  state := matsuoIndeterminateState
  evidence := matsuoProspectiveOCTTEvidence
  warrant := by
    intro b
    simp [matsuoProspectiveOCTTEvidence]
  continuity :=
    OriginOfLifeOCTT.ContinuityClass.indeterminate

theorem matsuo_c1_branch :
    OriginOfLifeOCTT.CarrierContinuityPositive
      matsuoC1World := by
  constructor
  · intro b
    rfl
  · rfl

theorem matsuo_c2_branch :
    OriginOfLifeOCTT.LineageContinuityPositive
      matsuoC2World := by
  constructor
  · intro b
    rfl
  · rfl

theorem matsuo_c3_branch :
    OriginOfLifeOCTT.NewCarrierProduction
      matsuoC3World := by
  constructor
  · intro b
    rfl
  · rfl

theorem matsuo_c5_branch :
    OriginOfLifeOCTT.PopulationPropagation
      matsuoC5World := by
  constructor
  · intro b
    rfl
  · rfl

theorem matsuo_indeterminate_branch :
    OriginOfLifeOCTT.OCTTIndeterminate
      matsuoIndeterminateWorld := by
  exact
    Or.inl
      ⟨OriginOfLifeOCTT.Burden.sourceAgeResolution,
       by
         simp [matsuoIndeterminateWorld, matsuoIndeterminateState]⟩

/-! --------------------------------------------------------------------------
One-control architecture marker
---------------------------------------------------------------------------- -/

inductive ControlArchitecture where
  | oneControl
  | differentiatedControls
deriving DecidableEq, Repr

def matsuoControlArchitecture :
    ControlArchitecture :=
  ControlArchitecture.oneControl

def hardyControlArchitecture :
    ControlArchitecture :=
  ControlArchitecture.differentiatedControls

theorem matsuo_is_one_control :
    matsuoControlArchitecture =
      ControlArchitecture.oneControl := by
  rfl

theorem hardy_is_differentiated_control :
    hardyControlArchitecture =
      ControlArchitecture.differentiatedControls := by
  rfl

/-! --------------------------------------------------------------------------
Matsuo branch 1:
OCTT succeeds, but mutual integration remains open
---------------------------------------------------------------------------- -/

/--
This is the conservative one-control branch.

Assume:
  * OCTT source / ancestry / passive-seed / maintenance / assay burdens close;
  * control efficacy closes;
  * endogeneity closes;
  * regeneration closes;
  * continued organizational competence closes;
  * assay adequacy closes;

but:

  AMC-3 MUTUAL INTEGRATION remains OPEN.

Then AMC remains INDETERMINATE.

This prevents OCTT success from deciding the one-control sufficiency question.
-/
def matsuoIntegrationOpenAMCState :
    OriginOfLifeAMC.Burden -> OriginOfLifeAMC.EvidenceState
  | .mutualIntegration => .open
  | _ => .discharged

def matsuoIntegrationOpenAMCWorld :
    OriginOfLifeAMC.World
      LifeOriginPublishedInstances.PublishedSystem
      LifeOriginPublishedInstances.PublishedEnvironment
      LifeOriginPublishedInstances.PublishedLevel
      LifeOriginPublishedInstances.PublishedScope
      LifeOriginPublishedInstances.PublishedHorizon
      LifeOriginPublishedInstances.PublishedBoundary
      LifeOriginPublishedInstances.PublishedProcess
      LifeOriginPublishedInstances.PublishedControl
    where
  pins := LifeOriginPublishedInstances.matsuoPins
  state := matsuoIntegrationOpenAMCState
  evidence := LifeOriginPublishedInstances.publishedAMCEvidence
  warrant := by
    intro b
    simp [LifeOriginPublishedInstances.publishedAMCEvidence]

theorem matsuo_integration_open_not_positive :
    ¬ OriginOfLifeAMC.AMCPositive
        matsuoIntegrationOpenAMCWorld := by
  intro hPos
  have h :=
    hPos OriginOfLifeAMC.Burden.mutualIntegration
  simp [matsuoIntegrationOpenAMCWorld,
        matsuoIntegrationOpenAMCState] at h

theorem matsuo_integration_open_not_negative :
    ¬ OriginOfLifeAMC.AMCNegative
        matsuoIntegrationOpenAMCWorld := by
  intro hNeg
  rcases hNeg with
    ⟨_hPins, _hAssay, b, hSubstantive, hViolated⟩
  cases b <;>
    simp [OriginOfLifeAMC.SubstantiveBurden,
          matsuoIntegrationOpenAMCWorld,
          matsuoIntegrationOpenAMCState] at hSubstantive hViolated

theorem matsuo_integration_open_is_indeterminate :
    OriginOfLifeAMC.AMCIndeterminate
      matsuoIntegrationOpenAMCWorld := by
  exact
    ⟨matsuo_integration_open_not_positive,
     matsuo_integration_open_not_negative⟩

theorem matsuo_c1_does_not_close_open_integration :
    OriginOfLifeOCTT.CarrierContinuityPositive matsuoC1World
    ∧ OriginOfLifeAMC.AMCIndeterminate
        matsuoIntegrationOpenAMCWorld := by
  exact
    ⟨matsuo_c1_branch,
     matsuo_integration_open_is_indeterminate⟩

theorem matsuo_c2_does_not_close_open_integration :
    OriginOfLifeOCTT.LineageContinuityPositive matsuoC2World
    ∧ OriginOfLifeAMC.AMCIndeterminate
        matsuoIntegrationOpenAMCWorld := by
  exact
    ⟨matsuo_c2_branch,
     matsuo_integration_open_is_indeterminate⟩

/-! --------------------------------------------------------------------------
Matsuo branch 2:
the one-control architecture independently discharges mutual integration
---------------------------------------------------------------------------- -/

/--
Strong adversarial AMC branch.

This world represents a future empirical result in which the Matsuo
one-control architecture lawfully discharges EVERY AMC burden, including
AMC-3 MUTUAL INTEGRATION.

The machine must admit that result.

Otherwise the contract would have secretly hard-coded the answer.
-/
def matsuoOneControlSuccessAMCState :
    OriginOfLifeAMC.Burden -> OriginOfLifeAMC.EvidenceState :=
  fun _ => OriginOfLifeAMC.EvidenceState.discharged

def matsuoOneControlSuccessAMCWorld :
    OriginOfLifeAMC.World
      LifeOriginPublishedInstances.PublishedSystem
      LifeOriginPublishedInstances.PublishedEnvironment
      LifeOriginPublishedInstances.PublishedLevel
      LifeOriginPublishedInstances.PublishedScope
      LifeOriginPublishedInstances.PublishedHorizon
      LifeOriginPublishedInstances.PublishedBoundary
      LifeOriginPublishedInstances.PublishedProcess
      LifeOriginPublishedInstances.PublishedControl
    where
  pins := LifeOriginPublishedInstances.matsuoPins
  state := matsuoOneControlSuccessAMCState
  evidence := LifeOriginPublishedInstances.publishedAMCEvidence
  warrant := by
    intro b
    simp [LifeOriginPublishedInstances.publishedAMCEvidence]

theorem matsuo_one_control_success_amc_positive :
    OriginOfLifeAMC.AMCPositive
      matsuoOneControlSuccessAMCWorld := by
  intro b
  rfl

/--
The current AMC contract does not encode a differentiated-control requirement.

This theorem is a synthetic prospective witness:

  ONE-CONTROL ARCHITECTURE
  +
  ALL AMC BURDENS DISCHARGED
  =
  AMC POSITIVE.

Whether the empirical Matsuo system ever reaches this branch remains open.
-/
theorem amc_contract_does_not_preinstall_differentiated_controls :
    matsuoControlArchitecture = ControlArchitecture.oneControl
    ∧ OriginOfLifeAMC.AMCPositive
        matsuoOneControlSuccessAMCWorld := by
  exact
    ⟨matsuo_is_one_control,
     matsuo_one_control_success_amc_positive⟩

/-! --------------------------------------------------------------------------
Explicit prospective differentiated-control hypothesis pressure
---------------------------------------------------------------------------- -/

/--
A deliberately separate research hypothesis:

"At the current candidate scope, a one-control Matsuo architecture cannot
satisfy AMC."

This is NOT part of the AMC contract.
-/
def DifferentiatedControlsNecessaryHypothesis : Prop :=
  ¬ OriginOfLifeAMC.AMCPositive
      matsuoOneControlSuccessAMCWorld

/--
If the future strong one-control branch is empirically earned, the separate
differentiated-controls-necessary hypothesis cannot be retained.

This is the adversarial pressure the Matsuo arm is meant to supply.
-/
theorem strong_matsuo_branch_incompatible_with_differentiated_necessity :
    ¬ DifferentiatedControlsNecessaryHypothesis := by
  intro hNecessary
  exact
    hNecessary matsuo_one_control_success_amc_positive

/-! --------------------------------------------------------------------------
Non-carrier Matsuo branches
---------------------------------------------------------------------------- -/

def matsuoNonCarrierAMCState :
    OriginOfLifeAMC.Burden -> OriginOfLifeAMC.EvidenceState
  | .continuedOrganizationalCompetence => .open
  | _ => .discharged

def matsuoNonCarrierAMCWorld :
    OriginOfLifeAMC.World
      LifeOriginPublishedInstances.PublishedSystem
      LifeOriginPublishedInstances.PublishedEnvironment
      LifeOriginPublishedInstances.PublishedLevel
      LifeOriginPublishedInstances.PublishedScope
      LifeOriginPublishedInstances.PublishedHorizon
      LifeOriginPublishedInstances.PublishedBoundary
      LifeOriginPublishedInstances.PublishedProcess
      LifeOriginPublishedInstances.PublishedControl
    where
  pins := LifeOriginPublishedInstances.matsuoPins
  state := matsuoNonCarrierAMCState
  evidence := LifeOriginPublishedInstances.publishedAMCEvidence
  warrant := by
    intro b
    simp [LifeOriginPublishedInstances.publishedAMCEvidence]

theorem matsuo_noncarrier_amc_not_positive :
    ¬ OriginOfLifeAMC.AMCPositive
        matsuoNonCarrierAMCWorld := by
  intro hPos
  have h :=
    hPos
      OriginOfLifeAMC.Burden.continuedOrganizationalCompetence
  simp [matsuoNonCarrierAMCWorld,
        matsuoNonCarrierAMCState] at h

theorem matsuo_noncarrier_amc_not_negative :
    ¬ OriginOfLifeAMC.AMCNegative
        matsuoNonCarrierAMCWorld := by
  intro hNeg
  rcases hNeg with
    ⟨_hPins, _hAssay, b, hSubstantive, hViolated⟩
  cases b <;>
    simp [OriginOfLifeAMC.SubstantiveBurden,
          matsuoNonCarrierAMCWorld,
          matsuoNonCarrierAMCState] at hSubstantive hViolated

theorem matsuo_noncarrier_amc_indeterminate :
    OriginOfLifeAMC.AMCIndeterminate
      matsuoNonCarrierAMCWorld := by
  exact
    ⟨matsuo_noncarrier_amc_not_positive,
     matsuo_noncarrier_amc_not_negative⟩

theorem matsuo_c3_keeps_carrier_amc_open :
    OriginOfLifeOCTT.NewCarrierProduction matsuoC3World
    ∧ OriginOfLifeAMC.AMCIndeterminate
        matsuoNonCarrierAMCWorld := by
  exact
    ⟨matsuo_c3_branch,
     matsuo_noncarrier_amc_indeterminate⟩

theorem matsuo_c5_keeps_carrier_amc_open :
    OriginOfLifeOCTT.PopulationPropagation matsuoC5World
    ∧ OriginOfLifeAMC.AMCIndeterminate
        matsuoNonCarrierAMCWorld := by
  exact
    ⟨matsuo_c5_branch,
     matsuo_noncarrier_amc_indeterminate⟩

/-! --------------------------------------------------------------------------
Prospective Matsuo public-translation world
---------------------------------------------------------------------------- -/

/-
Conditional endpoint only.

If:
  * one-control AMC is actually positive;
  * source / carrier / level / scope are pinned;
  * structural preservation is discharged;
  * every Life-specific object burden is discharged;
  * non-circularity and identity firewall remain discharged;

then the public translation may structurally conform.

This world is not the current evidence state.
-/

def matsuoProspectiveCoreState :
    UniversalTranslationContract.CoreBurden ->
    UniversalTranslationContract.Disposition :=
  fun _ => UniversalTranslationContract.Disposition.discharged

def matsuoProspectiveObjectState :
    LifeOriginPublicKernelAdapter.ObjectBurden ->
    UniversalTranslationContract.Disposition :=
  fun _ => UniversalTranslationContract.Disposition.discharged

def matsuoProspectiveDomainState :
    LifeOriginPublicKernelAdapter.DomainBurden ->
    UniversalTranslationContract.Disposition :=
  fun _ => UniversalTranslationContract.Disposition.discharged

noncomputable def matsuoProspectiveConformingWorld :
    UniversalTranslationContract.World
      LifeOriginPublicKernelAdapter.ObjectBurden
      LifeOriginPublicKernelAdapter.DomainBurden
    where

  coreState := matsuoProspectiveCoreState
  coreEvidence := fun b state =>
    state = matsuoProspectiveCoreState b
  coreWarrant := by
    intro b
    rfl

  objectRequired :=
    LifeOriginPublicKernelAdapter.objectRequired
  objectState := matsuoProspectiveObjectState
  objectEvidence := fun b state =>
    state = matsuoProspectiveObjectState b
  objectWarrant := by
    intro b _hRequired
    rfl

  domainEntryRequired :=
    LifeOriginPublicKernelAdapter.domainEntryRequired
  domainDownstreamRequired :=
    LifeOriginPublicKernelAdapter.domainDownstreamRequired
  domainRoleDisjoint :=
    LifeOriginPublicKernelAdapter.lifeOriginPublicWorld.domainRoleDisjoint

  domainState := matsuoProspectiveDomainState
  domainEvidence := fun b state =>
    state = matsuoProspectiveDomainState b
  domainWarrant := by
    intro b _hRequired
    rfl

theorem matsuo_prospective_translation_structural_conforms :
    UniversalTranslationContract.StructuralConforms
      matsuoProspectiveConformingWorld := by
  simp [UniversalTranslationContract.StructuralConforms,
        UniversalTranslationContract.GatingPass,
        matsuoProspectiveConformingWorld,
        matsuoProspectiveCoreState,
        matsuoProspectiveObjectState,
        matsuoProspectiveDomainState,
        LifeOriginPublicKernelAdapter.objectRequired,
        LifeOriginPublicKernelAdapter.domainEntryRequired]

/-! --------------------------------------------------------------------------
Prospective Matsuo endpoint branches
---------------------------------------------------------------------------- -/

/--
C1 with AMC-3 still OPEN:

OCTT carrier continuity may be positive while AMC remains indeterminate.
-/
theorem matsuo_c1_open_integration_endpoint :
    OriginOfLifeOCTT.CarrierContinuityPositive matsuoC1World
    ∧ OriginOfLifeAMC.AMCIndeterminate
        matsuoIntegrationOpenAMCWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨matsuo_c1_branch,
     matsuo_integration_open_is_indeterminate,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

/--
Strong C1 one-control branch:

Only if the one-control architecture independently discharges all AMC burdens
and all public translation burdens may the conditional endpoint conform.
-/
theorem matsuo_c1_full_contract_endpoint :
    OriginOfLifeOCTT.CarrierContinuityPositive matsuoC1World
    ∧ OriginOfLifeAMC.AMCPositive
        matsuoOneControlSuccessAMCWorld
    ∧ UniversalTranslationContract.StructuralConforms
        matsuoProspectiveConformingWorld := by
  exact
    ⟨matsuo_c1_branch,
     matsuo_one_control_success_amc_positive,
     matsuo_prospective_translation_structural_conforms⟩

/--
Strong C2 one-control branch.

No strict parent = daughter identity claim is made.
-/
theorem matsuo_c2_full_contract_endpoint :
    OriginOfLifeOCTT.LineageContinuityPositive matsuoC2World
    ∧ OriginOfLifeAMC.AMCPositive
        matsuoOneControlSuccessAMCWorld
    ∧ UniversalTranslationContract.StructuralConforms
        matsuoProspectiveConformingWorld := by
  exact
    ⟨matsuo_c2_branch,
     matsuo_one_control_success_amc_positive,
     matsuo_prospective_translation_structural_conforms⟩

theorem matsuo_c3_contract_endpoint :
    OriginOfLifeOCTT.NewCarrierProduction matsuoC3World
    ∧ OriginOfLifeAMC.AMCIndeterminate
        matsuoNonCarrierAMCWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨matsuo_c3_branch,
     matsuo_noncarrier_amc_indeterminate,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

theorem matsuo_c5_contract_endpoint :
    OriginOfLifeOCTT.PopulationPropagation matsuoC5World
    ∧ OriginOfLifeAMC.AMCIndeterminate
        matsuoNonCarrierAMCWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨matsuo_c5_branch,
     matsuo_noncarrier_amc_indeterminate,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

/-! --------------------------------------------------------------------------
Prospective Matsuo contract machine checkpoint
---------------------------------------------------------------------------- -/

theorem matsuo_prospective_adversarial_machine_checkpoint :
    OriginOfLifeOCTT.CarrierContinuityPositive matsuoC1World
    ∧ OriginOfLifeOCTT.LineageContinuityPositive matsuoC2World
    ∧ OriginOfLifeOCTT.NewCarrierProduction matsuoC3World
    ∧ OriginOfLifeOCTT.PopulationPropagation matsuoC5World
    ∧ OriginOfLifeOCTT.OCTTIndeterminate matsuoIndeterminateWorld
    ∧ OriginOfLifeAMC.AMCIndeterminate
        matsuoIntegrationOpenAMCWorld
    ∧ OriginOfLifeAMC.AMCPositive
        matsuoOneControlSuccessAMCWorld
    ∧ matsuoControlArchitecture = ControlArchitecture.oneControl
    ∧ ¬ DifferentiatedControlsNecessaryHypothesis
    ∧ UniversalTranslationContract.StructuralConforms
        matsuoProspectiveConformingWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨matsuo_c1_branch,
     matsuo_c2_branch,
     matsuo_c3_branch,
     matsuo_c5_branch,
     matsuo_indeterminate_branch,
     matsuo_integration_open_is_indeterminate,
     matsuo_one_control_success_amc_positive,
     matsuo_is_one_control,
     strong_matsuo_branch_incompatible_with_differentiated_necessity,
     matsuo_prospective_translation_structural_conforms,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

/-!
Machine-facing compression
--------------------------

CURRENT REAL MATSUO STATE:
  published AMC  = INDETERMINATE
  published OCTT = INDETERMINATE

PROSPECTIVE ADVERSARIAL BRANCHES:

  C1 / C2 + AMC-3 OPEN
    -> AMC INDETERMINATE

  C1 / C2 + one-control AMC-3 DISCHARGED
          + all other AMC burdens DISCHARGED
          + all translation burdens DISCHARGED
    -> AMC POSITIVE
    -> STRUCTURAL CONFORMS

  strong one-control AMC branch
    -> differentiated-controls-necessary hypothesis cannot be retained

  C3
    -> NEW-CARRIER PRODUCTION
    -> carrier AMC INDETERMINATE

  C5
    -> POPULATION PROPAGATION
    -> carrier AMC INDETERMINATE

The AMC contract does not preinstall the Hardy answer.
-/

end LifeOriginProspectiveMatsuo
end StructuralFlow


/-!
===============================================================================
WHOLE-PACKAGE MACHINE CLOSURE AUDIT v0.1
===============================================================================

Purpose
-------
Confirm that the complete append-only companion now contains, without kernel
repair:

  * confirmed scoped SF Life object;
  * AMC domain admission grammar;
  * OCTT evidence grammar;
  * current public adapter state;
  * Hardy published-state seats;
  * Matsuo published-state seats;
  * Hardy prospective experiment branches;
  * Matsuo prospective adversarial branches;
  * current evidence remaining NOT YET ADJUDICABLE.

This is a formal package-coherence audit.

It is not empirical closure.
===============================================================================
-/

namespace StructuralFlow
namespace LifeOriginWholePackageAudit

open UniversalTranslationContract

theorem whole_package_machine_closure_audit :
    PlusThree.SieveComplete
      (LifeChemistry.lifeWorld () ())
    ∧ OriginOfLifeAMC.AMCIndeterminate
        LifeOriginPublishedInstances.hardyAMCWorld
    ∧ OriginOfLifeOCTT.OCTTIndeterminate
        LifeOriginPublishedInstances.hardyOCTTWorld
    ∧ OriginOfLifeAMC.AMCIndeterminate
        LifeOriginPublishedInstances.matsuoAMCWorld
    ∧ OriginOfLifeOCTT.OCTTIndeterminate
        LifeOriginPublishedInstances.matsuoOCTTWorld
    ∧ OriginOfLifeOCTT.CarrierContinuityPositive
        LifeOriginProspectiveHardy.hardyC1World
    ∧ OriginOfLifeAMC.AMCPositive
        LifeOriginProspectiveHardy.hardyCarrierSuccessAMCWorld
    ∧ UniversalTranslationContract.StructuralConforms
        LifeOriginProspectiveHardy.hardyProspectiveConformingWorld
    ∧ OriginOfLifeOCTT.CarrierContinuityPositive
        LifeOriginProspectiveMatsuo.matsuoC1World
    ∧ OriginOfLifeAMC.AMCPositive
        LifeOriginProspectiveMatsuo.matsuoOneControlSuccessAMCWorld
    ∧ LifeOriginProspectiveMatsuo.matsuoControlArchitecture =
        LifeOriginProspectiveMatsuo.ControlArchitecture.oneControl
    ∧ ¬ LifeOriginProspectiveMatsuo.DifferentiatedControlsNecessaryHypothesis
    ∧ UniversalTranslationContract.StructuralConforms
        LifeOriginProspectiveMatsuo.matsuoProspectiveConformingWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨LifeChemistry.life_sieve_complete () (),
     LifeOriginPublishedInstances.hardy_amc_indeterminate,
     LifeOriginPublishedInstances.hardy_octt_indeterminate,
     LifeOriginPublishedInstances.matsuo_amc_indeterminate,
     LifeOriginPublishedInstances.matsuo_octt_indeterminate,
     LifeOriginProspectiveHardy.hardy_c1_branch,
     LifeOriginProspectiveHardy.hardy_success_branch_amc_positive,
     LifeOriginProspectiveHardy.hardy_prospective_translation_structural_conforms,
     LifeOriginProspectiveMatsuo.matsuo_c1_branch,
     LifeOriginProspectiveMatsuo.matsuo_one_control_success_amc_positive,
     LifeOriginProspectiveMatsuo.matsuo_is_one_control,
     LifeOriginProspectiveMatsuo.strong_matsuo_branch_incompatible_with_differentiated_necessity,
     LifeOriginProspectiveMatsuo.matsuo_prospective_translation_structural_conforms,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

/--
The current real package remains empirically open even though both prospective
success endpoints are formally available.
-/
theorem prospective_endpoints_do_not_mutate_current_evidence :
    UniversalTranslationContract.StructuralConforms
        LifeOriginProspectiveHardy.hardyProspectiveConformingWorld
    ∧ UniversalTranslationContract.StructuralConforms
        LifeOriginProspectiveMatsuo.matsuoProspectiveConformingWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨LifeOriginProspectiveHardy.hardy_prospective_translation_structural_conforms,
     LifeOriginProspectiveMatsuo.matsuo_prospective_translation_structural_conforms,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

/-!
Final machine-facing compression
--------------------------------

UNCHANGED UNIVERSAL KERNEL
+
APPEND-ONLY LIFE / ORIGIN-OF-LIFE COMPANION

CURRENT:
  SF LIFE OBJECT             = MACHINE-CONFIRMED
  HARDY PUBLISHED AMC/OCTT   = INDETERMINATE
  MATSUO PUBLISHED AMC/OCTT  = INDETERMINATE
  PUBLIC TRANSLATION         = NOT YET ADJUDICABLE

PROSPECTIVE:
  HARDY C1/C2 + full AMC + full translation
    -> STRUCTURAL CONFORMS

  MATSUO C1/C2 + AMC-3 still open
    -> AMC INDETERMINATE

  MATSUO C1/C2 + lawful one-control AMC completion + full translation
    -> STRUCTURAL CONFORMS
    -> differentiated-controls-necessary hypothesis cannot survive

  C3 / C5 branches
    -> remain weaker carrier-level results

No empirical branch has been asserted.
No Universal Kernel repair is encoded or required by this package.
-/

end LifeOriginWholePackageAudit
end StructuralFlow

/-!
===============================================================================
C4 DISSOLUTION / RECONSTITUTION PROSPECTIVE BRANCH COMPLETION v0.1
===============================================================================

ROLE
----
Complete the system-specific prospective OCTT result grammar for the already
defined generic C4 continuity class:

  C4 — dissolution / reconstitution.

The generic OCTT contract already admitted C4 through
OriginOfLifeOCTT.Reconstitution.

Earlier Hardy / Matsuo prospective seats explicitly specialized C1, C2, C3,
C5, and INDETERMINATE.  This append supplies the missing system-specific C4
downstream branch without changing any earlier burden, current literature
state, public adapter state, or Universal Kernel structure.

C4 remains weaker than continuous-carrier or daughter-lineage continuity.
At the bounded-carrier AMC scope used here, C4 therefore keeps continued
organizational competence OPEN unless separately earned at another declared
level / scope.

No empirical C4 result is asserted.
===============================================================================
-/

namespace StructuralFlow
namespace LifeOriginC4Completion

open OriginOfLifeAMC
open OriginOfLifeOCTT
open LifeOriginPublicKernelAdapter
open UniversalTranslationContract

/-! --------------------------------------------------------------------------
Hardy C4
---------------------------------------------------------------------------- -/

def hardyC4World :
    OriginOfLifeOCTT.World where
  state := LifeOriginProspectiveHardy.hardyExecutedOCTTState
  evidence := LifeOriginProspectiveHardy.prospectiveOCTTEvidence
  warrant := by
    intro b
    simp [LifeOriginProspectiveHardy.prospectiveOCTTEvidence]
  continuity :=
    OriginOfLifeOCTT.ContinuityClass.dissolutionReconstitution

theorem hardy_c4_branch :
    OriginOfLifeOCTT.Reconstitution hardyC4World := by
  constructor
  · intro b
    rfl
  · rfl

theorem hardy_c4_contract_endpoint :
    OriginOfLifeOCTT.Reconstitution hardyC4World
    ∧ OriginOfLifeAMC.AMCIndeterminate
        LifeOriginProspectiveHardy.hardyNonCarrierAMCWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨hardy_c4_branch,
     LifeOriginProspectiveHardy.hardy_noncarrier_amc_indeterminate,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

/-! --------------------------------------------------------------------------
Matsuo C4
---------------------------------------------------------------------------- -/

def matsuoC4World :
    OriginOfLifeOCTT.World where
  state := LifeOriginProspectiveMatsuo.matsuoExecutedOCTTState
  evidence := LifeOriginProspectiveMatsuo.matsuoProspectiveOCTTEvidence
  warrant := by
    intro b
    simp [LifeOriginProspectiveMatsuo.matsuoProspectiveOCTTEvidence]
  continuity :=
    OriginOfLifeOCTT.ContinuityClass.dissolutionReconstitution

theorem matsuo_c4_branch :
    OriginOfLifeOCTT.Reconstitution matsuoC4World := by
  constructor
  · intro b
    rfl
  · rfl

theorem matsuo_c4_contract_endpoint :
    OriginOfLifeOCTT.Reconstitution matsuoC4World
    ∧ OriginOfLifeAMC.AMCIndeterminate
        LifeOriginProspectiveMatsuo.matsuoNonCarrierAMCWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨matsuo_c4_branch,
     LifeOriginProspectiveMatsuo.matsuo_noncarrier_amc_indeterminate,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

/-! --------------------------------------------------------------------------
C4 completion machine checkpoint
---------------------------------------------------------------------------- -/

theorem c4_completion_machine_checkpoint :
    OriginOfLifeOCTT.Reconstitution hardyC4World
    ∧ OriginOfLifeAMC.AMCIndeterminate
        LifeOriginProspectiveHardy.hardyNonCarrierAMCWorld
    ∧ OriginOfLifeOCTT.Reconstitution matsuoC4World
    ∧ OriginOfLifeAMC.AMCIndeterminate
        LifeOriginProspectiveMatsuo.matsuoNonCarrierAMCWorld
    ∧ UniversalTranslationContract.NotYetAdjudicable
        LifeOriginPublicKernelAdapter.lifeOriginPublicWorld := by
  exact
    ⟨hardy_c4_branch,
     LifeOriginProspectiveHardy.hardy_noncarrier_amc_indeterminate,
     matsuo_c4_branch,
     LifeOriginProspectiveMatsuo.matsuo_noncarrier_amc_indeterminate,
     LifeOriginPublicKernelAdapter.life_origin_public_kernel_not_yet_adjudicable⟩

/-!
Machine-facing compression
--------------------------

C4 HARDY:
  DISSOLUTION / RECONSTITUTION
  -> bounded-carrier AMC remains INDETERMINATE
  -> current public translation remains NOT YET ADJUDICABLE.

C4 MATSUO:
  DISSOLUTION / RECONSTITUTION
  -> bounded-carrier AMC remains INDETERMINATE
  -> current public translation remains NOT YET ADJUDICABLE.

No prior branch changes.
No empirical result manufactured.
No Universal Kernel repair required.
-/

end LifeOriginC4Completion
end StructuralFlow
