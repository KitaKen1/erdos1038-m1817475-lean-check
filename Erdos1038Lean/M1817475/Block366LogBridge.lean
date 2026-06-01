import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block366

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block366

open Set

def block366W1 : Rat := ((2186898988487351 : Rat) / 2500000000000000)
def block366W2 : Rat := ((4733096984842219 : Rat) / 100000000000000000)
def block366W3 : Rat := ((384033887414643 : Rat) / 2500000000000000)
def block366W4 : Rat := ((13942858982528347 : Rat) / 100000000000000000)
def block366S1 : Rat := ((18174751 : Rat) / 10000000)
def block366S2 : Rat := ((511587 : Rat) / 200000)
def block366S3 : Rat := ((132978584017857142891 : Rat) / 50000000000000000000)
def block366S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block366V (y : ℝ) : ℝ :=
  ratPotential block366W1 block366W2 block366W3 block366W4 block366S1 block366S2 block366S3 block366S4 y

def block366LeftParamsCertificate : Bool :=
  allBoxesSameParams block366LeftBoxes block366W1 block366W2 block366W3 block366W4 block366S1 block366S2 block366S3 block366S4

theorem block366LeftParamsCertificate_eq_true :
    block366LeftParamsCertificate = true := by
  native_decide

theorem block366_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block366LeftL : ℝ) (block366LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block366S1 : ℝ))
    (hy2ne : y ≠ (block366S2 : ℝ))
    (hy3ne : y ≠ (block366S3 : ℝ))
    (hy4ne : y ≠ (block366S4 : ℝ)) :
    0 < block366V y := by
  have hcert := block366LeftCertificate_eq_true
  unfold block366LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block366LeftBoxes) (lo := block366LeftL) (hi := block366LeftR)
    (w1 := block366W1) (w2 := block366W2) (w3 := block366W3) (w4 := block366W4)
    (s1 := block366S1) (s2 := block366S2) (s3 := block366S3) (s4 := block366S4)
    hboxes hcover block366LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block366RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block366RightChunk000 block366W1 block366W2 block366W3 block366W4 block366S1 block366S2 block366S3 block366S4

theorem block366RightChunk000ParamsCertificate_eq_true :
    block366RightChunk000ParamsCertificate = true := by
  native_decide

theorem block366_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block366RightChunk000L : ℝ) (block366RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block366S1 : ℝ))
    (hy2ne : y ≠ (block366S2 : ℝ))
    (hy3ne : y ≠ (block366S3 : ℝ))
    (hy4ne : y ≠ (block366S4 : ℝ)) :
    0 < block366V y := by
  have hcert := block366RightChunk000Certificate_eq_true
  unfold block366RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block366RightChunk000) (lo := block366RightChunk000L) (hi := block366RightChunk000R)
    (w1 := block366W1) (w2 := block366W2) (w3 := block366W3) (w4 := block366W4)
    (s1 := block366S1) (s2 := block366S2) (s3 := block366S3) (s4 := block366S4)
    hboxes hcover block366RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block366_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block366RightL : ℝ) (block366RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block366S1 : ℝ))
    (hy2ne : y ≠ (block366S2 : ℝ))
    (hy3ne : y ≠ (block366S3 : ℝ))
    (hy4ne : y ≠ (block366S4 : ℝ)) :
    0 < block366V y := by
  have hL : (block366RightChunk000L : ℝ) = (block366RightL : ℝ) := by
    norm_num [block366RightChunk000L, block366RightL]
  have hR : (block366RightChunk000R : ℝ) = (block366RightR : ℝ) := by
    norm_num [block366RightChunk000R, block366RightR]
  have hyc : y ∈ Icc (block366RightChunk000L : ℝ) (block366RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block366_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block366_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block366LeftL : ℝ) (block366LeftR : ℝ) →
    y ≠ 0 → y ≠ (block366S1 : ℝ) → y ≠ (block366S2 : ℝ) →
    y ≠ (block366S3 : ℝ) → y ≠ (block366S4 : ℝ) → 0 < block366V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block366RightL : ℝ) (block366RightR : ℝ) →
    y ≠ 0 → y ≠ (block366S1 : ℝ) → y ≠ (block366S2 : ℝ) →
    y ≠ (block366S3 : ℝ) → y ≠ (block366S4 : ℝ) → 0 < block366V y)

theorem block366_reallog_certificate_proof :
    block366_reallog_certificate := by
  exact ⟨block366_left_V_pos, block366_right_V_pos⟩

end Block366
end M1817475
end Erdos1038Lean
