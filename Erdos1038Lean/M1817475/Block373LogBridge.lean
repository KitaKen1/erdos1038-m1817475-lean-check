import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block373

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block373

open Set

def block373W1 : Rat := ((1077681018310393 : Rat) / 1250000000000000)
def block373W2 : Rat := ((11727769600462271 : Rat) / 250000000000000000)
def block373W3 : Rat := ((48733178843473 : Rat) / 312500000000000)
def block373W4 : Rat := ((13986592798100433 : Rat) / 100000000000000000)
def block373S1 : Rat := ((18174751 : Rat) / 10000000)
def block373S2 : Rat := ((511587 : Rat) / 200000)
def block373S3 : Rat := ((132841740267857142897 : Rat) / 50000000000000000000)
def block373S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block373V (y : ℝ) : ℝ :=
  ratPotential block373W1 block373W2 block373W3 block373W4 block373S1 block373S2 block373S3 block373S4 y

def block373LeftParamsCertificate : Bool :=
  allBoxesSameParams block373LeftBoxes block373W1 block373W2 block373W3 block373W4 block373S1 block373S2 block373S3 block373S4

theorem block373LeftParamsCertificate_eq_true :
    block373LeftParamsCertificate = true := by
  native_decide

theorem block373_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block373LeftL : ℝ) (block373LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block373S1 : ℝ))
    (hy2ne : y ≠ (block373S2 : ℝ))
    (hy3ne : y ≠ (block373S3 : ℝ))
    (hy4ne : y ≠ (block373S4 : ℝ)) :
    0 < block373V y := by
  have hcert := block373LeftCertificate_eq_true
  unfold block373LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block373LeftBoxes) (lo := block373LeftL) (hi := block373LeftR)
    (w1 := block373W1) (w2 := block373W2) (w3 := block373W3) (w4 := block373W4)
    (s1 := block373S1) (s2 := block373S2) (s3 := block373S3) (s4 := block373S4)
    hboxes hcover block373LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block373RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block373RightChunk000 block373W1 block373W2 block373W3 block373W4 block373S1 block373S2 block373S3 block373S4

theorem block373RightChunk000ParamsCertificate_eq_true :
    block373RightChunk000ParamsCertificate = true := by
  native_decide

theorem block373_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block373RightChunk000L : ℝ) (block373RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block373S1 : ℝ))
    (hy2ne : y ≠ (block373S2 : ℝ))
    (hy3ne : y ≠ (block373S3 : ℝ))
    (hy4ne : y ≠ (block373S4 : ℝ)) :
    0 < block373V y := by
  have hcert := block373RightChunk000Certificate_eq_true
  unfold block373RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block373RightChunk000) (lo := block373RightChunk000L) (hi := block373RightChunk000R)
    (w1 := block373W1) (w2 := block373W2) (w3 := block373W3) (w4 := block373W4)
    (s1 := block373S1) (s2 := block373S2) (s3 := block373S3) (s4 := block373S4)
    hboxes hcover block373RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block373_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block373RightL : ℝ) (block373RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block373S1 : ℝ))
    (hy2ne : y ≠ (block373S2 : ℝ))
    (hy3ne : y ≠ (block373S3 : ℝ))
    (hy4ne : y ≠ (block373S4 : ℝ)) :
    0 < block373V y := by
  have hL : (block373RightChunk000L : ℝ) = (block373RightL : ℝ) := by
    norm_num [block373RightChunk000L, block373RightL]
  have hR : (block373RightChunk000R : ℝ) = (block373RightR : ℝ) := by
    norm_num [block373RightChunk000R, block373RightR]
  have hyc : y ∈ Icc (block373RightChunk000L : ℝ) (block373RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block373_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block373_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block373LeftL : ℝ) (block373LeftR : ℝ) →
    y ≠ 0 → y ≠ (block373S1 : ℝ) → y ≠ (block373S2 : ℝ) →
    y ≠ (block373S3 : ℝ) → y ≠ (block373S4 : ℝ) → 0 < block373V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block373RightL : ℝ) (block373RightR : ℝ) →
    y ≠ 0 → y ≠ (block373S1 : ℝ) → y ≠ (block373S2 : ℝ) →
    y ≠ (block373S3 : ℝ) → y ≠ (block373S4 : ℝ) → 0 < block373V y)

theorem block373_reallog_certificate_proof :
    block373_reallog_certificate := by
  exact ⟨block373_left_V_pos, block373_right_V_pos⟩

end Block373
end M1817475
end Erdos1038Lean
