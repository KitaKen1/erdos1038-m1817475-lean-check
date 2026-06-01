import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block451

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block451

open Set

def block451W1 : Rat := ((5947590650675443 : Rat) / 10000000000000000)
def block451W2 : Rat := (0 : Rat)
def block451W3 : Rat := ((3342252718433901 : Rat) / 10000000000000000)
def block451W4 : Rat := ((207981294197139 : Rat) / 3125000000000000)
def block451S1 : Rat := ((18174751 : Rat) / 10000000)
def block451S2 : Rat := ((511587 : Rat) / 200000)
def block451S3 : Rat := ((131316909910714285821 : Rat) / 50000000000000000000)
def block451S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block451V (y : ℝ) : ℝ :=
  ratPotential block451W1 block451W2 block451W3 block451W4 block451S1 block451S2 block451S3 block451S4 y

def block451LeftParamsCertificate : Bool :=
  allBoxesSameParams block451LeftBoxes block451W1 block451W2 block451W3 block451W4 block451S1 block451S2 block451S3 block451S4

theorem block451LeftParamsCertificate_eq_true :
    block451LeftParamsCertificate = true := by
  native_decide

theorem block451_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block451LeftL : ℝ) (block451LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block451S1 : ℝ))
    (hy2ne : y ≠ (block451S2 : ℝ))
    (hy3ne : y ≠ (block451S3 : ℝ))
    (hy4ne : y ≠ (block451S4 : ℝ)) :
    0 < block451V y := by
  have hcert := block451LeftCertificate_eq_true
  unfold block451LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block451LeftBoxes) (lo := block451LeftL) (hi := block451LeftR)
    (w1 := block451W1) (w2 := block451W2) (w3 := block451W3) (w4 := block451W4)
    (s1 := block451S1) (s2 := block451S2) (s3 := block451S3) (s4 := block451S4)
    hboxes hcover block451LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block451RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block451RightChunk000 block451W1 block451W2 block451W3 block451W4 block451S1 block451S2 block451S3 block451S4

theorem block451RightChunk000ParamsCertificate_eq_true :
    block451RightChunk000ParamsCertificate = true := by
  native_decide

theorem block451_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block451RightChunk000L : ℝ) (block451RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block451S1 : ℝ))
    (hy2ne : y ≠ (block451S2 : ℝ))
    (hy3ne : y ≠ (block451S3 : ℝ))
    (hy4ne : y ≠ (block451S4 : ℝ)) :
    0 < block451V y := by
  have hcert := block451RightChunk000Certificate_eq_true
  unfold block451RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block451RightChunk000) (lo := block451RightChunk000L) (hi := block451RightChunk000R)
    (w1 := block451W1) (w2 := block451W2) (w3 := block451W3) (w4 := block451W4)
    (s1 := block451S1) (s2 := block451S2) (s3 := block451S3) (s4 := block451S4)
    hboxes hcover block451RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block451_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block451RightL : ℝ) (block451RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block451S1 : ℝ))
    (hy2ne : y ≠ (block451S2 : ℝ))
    (hy3ne : y ≠ (block451S3 : ℝ))
    (hy4ne : y ≠ (block451S4 : ℝ)) :
    0 < block451V y := by
  have hL : (block451RightChunk000L : ℝ) = (block451RightL : ℝ) := by
    norm_num [block451RightChunk000L, block451RightL]
  have hR : (block451RightChunk000R : ℝ) = (block451RightR : ℝ) := by
    norm_num [block451RightChunk000R, block451RightR]
  have hyc : y ∈ Icc (block451RightChunk000L : ℝ) (block451RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block451_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block451_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block451LeftL : ℝ) (block451LeftR : ℝ) →
    y ≠ 0 → y ≠ (block451S1 : ℝ) → y ≠ (block451S2 : ℝ) →
    y ≠ (block451S3 : ℝ) → y ≠ (block451S4 : ℝ) → 0 < block451V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block451RightL : ℝ) (block451RightR : ℝ) →
    y ≠ 0 → y ≠ (block451S1 : ℝ) → y ≠ (block451S2 : ℝ) →
    y ≠ (block451S3 : ℝ) → y ≠ (block451S4 : ℝ) → 0 < block451V y)

theorem block451_reallog_certificate_proof :
    block451_reallog_certificate := by
  exact ⟨block451_left_V_pos, block451_right_V_pos⟩

end Block451
end M1817475
end Erdos1038Lean
