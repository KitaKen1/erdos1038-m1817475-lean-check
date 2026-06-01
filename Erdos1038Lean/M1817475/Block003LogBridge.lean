import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block003

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block003

open Set

def block003W1 : Rat := ((1310319917907001 : Rat) / 100000000000000)
def block003W2 : Rat := (0 : Rat)
def block003W3 : Rat := (0 : Rat)
def block003W4 : Rat := ((497390689407017 : Rat) / 2000000000000000)
def block003S1 : Rat := ((18174751 : Rat) / 10000000)
def block003S2 : Rat := ((511587 : Rat) / 200000)
def block003S3 : Rat := ((107000619 : Rat) / 40000000)
def block003S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block003V (y : ℝ) : ℝ :=
  ratPotential block003W1 block003W2 block003W3 block003W4 block003S1 block003S2 block003S3 block003S4 y

def block003LeftParamsCertificate : Bool :=
  allBoxesSameParams block003LeftBoxes block003W1 block003W2 block003W3 block003W4 block003S1 block003S2 block003S3 block003S4

theorem block003LeftParamsCertificate_eq_true :
    block003LeftParamsCertificate = true := by
  native_decide

theorem block003_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block003LeftL : ℝ) (block003LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block003S1 : ℝ))
    (hy2ne : y ≠ (block003S2 : ℝ))
    (hy3ne : y ≠ (block003S3 : ℝ))
    (hy4ne : y ≠ (block003S4 : ℝ)) :
    0 < block003V y := by
  have hcert := block003LeftCertificate_eq_true
  unfold block003LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block003LeftBoxes) (lo := block003LeftL) (hi := block003LeftR)
    (w1 := block003W1) (w2 := block003W2) (w3 := block003W3) (w4 := block003W4)
    (s1 := block003S1) (s2 := block003S2) (s3 := block003S3) (s4 := block003S4)
    hboxes hcover block003LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block003RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block003RightChunk000 block003W1 block003W2 block003W3 block003W4 block003S1 block003S2 block003S3 block003S4

theorem block003RightChunk000ParamsCertificate_eq_true :
    block003RightChunk000ParamsCertificate = true := by
  native_decide

theorem block003_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block003RightChunk000L : ℝ) (block003RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block003S1 : ℝ))
    (hy2ne : y ≠ (block003S2 : ℝ))
    (hy3ne : y ≠ (block003S3 : ℝ))
    (hy4ne : y ≠ (block003S4 : ℝ)) :
    0 < block003V y := by
  have hcert := block003RightChunk000Certificate_eq_true
  unfold block003RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block003RightChunk000) (lo := block003RightChunk000L) (hi := block003RightChunk000R)
    (w1 := block003W1) (w2 := block003W2) (w3 := block003W3) (w4 := block003W4)
    (s1 := block003S1) (s2 := block003S2) (s3 := block003S3) (s4 := block003S4)
    hboxes hcover block003RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block003_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block003RightL : ℝ) (block003RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block003S1 : ℝ))
    (hy2ne : y ≠ (block003S2 : ℝ))
    (hy3ne : y ≠ (block003S3 : ℝ))
    (hy4ne : y ≠ (block003S4 : ℝ)) :
    0 < block003V y := by
  have hL : (block003RightChunk000L : ℝ) = (block003RightL : ℝ) := by
    norm_num [block003RightChunk000L, block003RightL]
  have hR : (block003RightChunk000R : ℝ) = (block003RightR : ℝ) := by
    norm_num [block003RightChunk000R, block003RightR]
  have hyc : y ∈ Icc (block003RightChunk000L : ℝ) (block003RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block003_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block003_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block003LeftL : ℝ) (block003LeftR : ℝ) →
    y ≠ 0 → y ≠ (block003S1 : ℝ) → y ≠ (block003S2 : ℝ) →
    y ≠ (block003S3 : ℝ) → y ≠ (block003S4 : ℝ) → 0 < block003V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block003RightL : ℝ) (block003RightR : ℝ) →
    y ≠ 0 → y ≠ (block003S1 : ℝ) → y ≠ (block003S2 : ℝ) →
    y ≠ (block003S3 : ℝ) → y ≠ (block003S4 : ℝ) → 0 < block003V y)

theorem block003_reallog_certificate_proof :
    block003_reallog_certificate := by
  exact ⟨block003_left_V_pos, block003_right_V_pos⟩

end Block003
end M1817475
end Erdos1038Lean
