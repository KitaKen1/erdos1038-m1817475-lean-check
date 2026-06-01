import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block199

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block199

open Set

def block199W1 : Rat := ((9733225140454937 : Rat) / 10000000000000000)
def block199W2 : Rat := ((6357070269599 : Rat) / 125000000000000)
def block199W3 : Rat := ((556548227516223 : Rat) / 3125000000000000)
def block199W4 : Rat := ((4798779455663451 : Rat) / 50000000000000000)
def block199S1 : Rat := ((18174751 : Rat) / 10000000)
def block199S2 : Rat := ((511587 : Rat) / 200000)
def block199S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block199S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block199V (y : ℝ) : ℝ :=
  ratPotential block199W1 block199W2 block199W3 block199W4 block199S1 block199S2 block199S3 block199S4 y

def block199LeftParamsCertificate : Bool :=
  allBoxesSameParams block199LeftBoxes block199W1 block199W2 block199W3 block199W4 block199S1 block199S2 block199S3 block199S4

theorem block199LeftParamsCertificate_eq_true :
    block199LeftParamsCertificate = true := by
  native_decide

theorem block199_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block199LeftL : ℝ) (block199LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block199S1 : ℝ))
    (hy2ne : y ≠ (block199S2 : ℝ))
    (hy3ne : y ≠ (block199S3 : ℝ))
    (hy4ne : y ≠ (block199S4 : ℝ)) :
    0 < block199V y := by
  have hcert := block199LeftCertificate_eq_true
  unfold block199LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block199LeftBoxes) (lo := block199LeftL) (hi := block199LeftR)
    (w1 := block199W1) (w2 := block199W2) (w3 := block199W3) (w4 := block199W4)
    (s1 := block199S1) (s2 := block199S2) (s3 := block199S3) (s4 := block199S4)
    hboxes hcover block199LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block199RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block199RightChunk000 block199W1 block199W2 block199W3 block199W4 block199S1 block199S2 block199S3 block199S4

theorem block199RightChunk000ParamsCertificate_eq_true :
    block199RightChunk000ParamsCertificate = true := by
  native_decide

theorem block199_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block199RightChunk000L : ℝ) (block199RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block199S1 : ℝ))
    (hy2ne : y ≠ (block199S2 : ℝ))
    (hy3ne : y ≠ (block199S3 : ℝ))
    (hy4ne : y ≠ (block199S4 : ℝ)) :
    0 < block199V y := by
  have hcert := block199RightChunk000Certificate_eq_true
  unfold block199RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block199RightChunk000) (lo := block199RightChunk000L) (hi := block199RightChunk000R)
    (w1 := block199W1) (w2 := block199W2) (w3 := block199W3) (w4 := block199W4)
    (s1 := block199S1) (s2 := block199S2) (s3 := block199S3) (s4 := block199S4)
    hboxes hcover block199RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block199RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block199RightChunk001 block199W1 block199W2 block199W3 block199W4 block199S1 block199S2 block199S3 block199S4

theorem block199RightChunk001ParamsCertificate_eq_true :
    block199RightChunk001ParamsCertificate = true := by
  native_decide

theorem block199_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block199RightChunk001L : ℝ) (block199RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block199S1 : ℝ))
    (hy2ne : y ≠ (block199S2 : ℝ))
    (hy3ne : y ≠ (block199S3 : ℝ))
    (hy4ne : y ≠ (block199S4 : ℝ)) :
    0 < block199V y := by
  have hcert := block199RightChunk001Certificate_eq_true
  unfold block199RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block199RightChunk001) (lo := block199RightChunk001L) (hi := block199RightChunk001R)
    (w1 := block199W1) (w2 := block199W2) (w3 := block199W3) (w4 := block199W4)
    (s1 := block199S1) (s2 := block199S2) (s3 := block199S3) (s4 := block199S4)
    hboxes hcover block199RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block199RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block199RightChunk002 block199W1 block199W2 block199W3 block199W4 block199S1 block199S2 block199S3 block199S4

theorem block199RightChunk002ParamsCertificate_eq_true :
    block199RightChunk002ParamsCertificate = true := by
  native_decide

theorem block199_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block199RightChunk002L : ℝ) (block199RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block199S1 : ℝ))
    (hy2ne : y ≠ (block199S2 : ℝ))
    (hy3ne : y ≠ (block199S3 : ℝ))
    (hy4ne : y ≠ (block199S4 : ℝ)) :
    0 < block199V y := by
  have hcert := block199RightChunk002Certificate_eq_true
  unfold block199RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block199RightChunk002) (lo := block199RightChunk002L) (hi := block199RightChunk002R)
    (w1 := block199W1) (w2 := block199W2) (w3 := block199W3) (w4 := block199W4)
    (s1 := block199S1) (s2 := block199S2) (s3 := block199S3) (s4 := block199S4)
    hboxes hcover block199RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block199RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block199RightChunk003 block199W1 block199W2 block199W3 block199W4 block199S1 block199S2 block199S3 block199S4

theorem block199RightChunk003ParamsCertificate_eq_true :
    block199RightChunk003ParamsCertificate = true := by
  native_decide

theorem block199_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block199RightChunk003L : ℝ) (block199RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block199S1 : ℝ))
    (hy2ne : y ≠ (block199S2 : ℝ))
    (hy3ne : y ≠ (block199S3 : ℝ))
    (hy4ne : y ≠ (block199S4 : ℝ)) :
    0 < block199V y := by
  have hcert := block199RightChunk003Certificate_eq_true
  unfold block199RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block199RightChunk003) (lo := block199RightChunk003L) (hi := block199RightChunk003R)
    (w1 := block199W1) (w2 := block199W2) (w3 := block199W3) (w4 := block199W4)
    (s1 := block199S1) (s2 := block199S2) (s3 := block199S3) (s4 := block199S4)
    hboxes hcover block199RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block199RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block199RightChunk004 block199W1 block199W2 block199W3 block199W4 block199S1 block199S2 block199S3 block199S4

theorem block199RightChunk004ParamsCertificate_eq_true :
    block199RightChunk004ParamsCertificate = true := by
  native_decide

theorem block199_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block199RightChunk004L : ℝ) (block199RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block199S1 : ℝ))
    (hy2ne : y ≠ (block199S2 : ℝ))
    (hy3ne : y ≠ (block199S3 : ℝ))
    (hy4ne : y ≠ (block199S4 : ℝ)) :
    0 < block199V y := by
  have hcert := block199RightChunk004Certificate_eq_true
  unfold block199RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block199RightChunk004) (lo := block199RightChunk004L) (hi := block199RightChunk004R)
    (w1 := block199W1) (w2 := block199W2) (w3 := block199W3) (w4 := block199W4)
    (s1 := block199S1) (s2 := block199S2) (s3 := block199S3) (s4 := block199S4)
    hboxes hcover block199RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block199RightChunk005ParamsCertificate : Bool :=
  allBoxesSameParams block199RightChunk005 block199W1 block199W2 block199W3 block199W4 block199S1 block199S2 block199S3 block199S4

theorem block199RightChunk005ParamsCertificate_eq_true :
    block199RightChunk005ParamsCertificate = true := by
  native_decide

theorem block199_right_chunk005_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block199RightChunk005L : ℝ) (block199RightChunk005R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block199S1 : ℝ))
    (hy2ne : y ≠ (block199S2 : ℝ))
    (hy3ne : y ≠ (block199S3 : ℝ))
    (hy4ne : y ≠ (block199S4 : ℝ)) :
    0 < block199V y := by
  have hcert := block199RightChunk005Certificate_eq_true
  unfold block199RightChunk005Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block199RightChunk005) (lo := block199RightChunk005L) (hi := block199RightChunk005R)
    (w1 := block199W1) (w2 := block199W2) (w3 := block199W3) (w4 := block199W4)
    (s1 := block199S1) (s2 := block199S2) (s3 := block199S3) (s4 := block199S4)
    hboxes hcover block199RightChunk005ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block199RightChunk006ParamsCertificate : Bool :=
  allBoxesSameParams block199RightChunk006 block199W1 block199W2 block199W3 block199W4 block199S1 block199S2 block199S3 block199S4

theorem block199RightChunk006ParamsCertificate_eq_true :
    block199RightChunk006ParamsCertificate = true := by
  native_decide

theorem block199_right_chunk006_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block199RightChunk006L : ℝ) (block199RightChunk006R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block199S1 : ℝ))
    (hy2ne : y ≠ (block199S2 : ℝ))
    (hy3ne : y ≠ (block199S3 : ℝ))
    (hy4ne : y ≠ (block199S4 : ℝ)) :
    0 < block199V y := by
  have hcert := block199RightChunk006Certificate_eq_true
  unfold block199RightChunk006Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block199RightChunk006) (lo := block199RightChunk006L) (hi := block199RightChunk006R)
    (w1 := block199W1) (w2 := block199W2) (w3 := block199W3) (w4 := block199W4)
    (s1 := block199S1) (s2 := block199S2) (s3 := block199S3) (s4 := block199S4)
    hboxes hcover block199RightChunk006ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block199RightChunk007ParamsCertificate : Bool :=
  allBoxesSameParams block199RightChunk007 block199W1 block199W2 block199W3 block199W4 block199S1 block199S2 block199S3 block199S4

theorem block199RightChunk007ParamsCertificate_eq_true :
    block199RightChunk007ParamsCertificate = true := by
  native_decide

theorem block199_right_chunk007_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block199RightChunk007L : ℝ) (block199RightChunk007R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block199S1 : ℝ))
    (hy2ne : y ≠ (block199S2 : ℝ))
    (hy3ne : y ≠ (block199S3 : ℝ))
    (hy4ne : y ≠ (block199S4 : ℝ)) :
    0 < block199V y := by
  have hcert := block199RightChunk007Certificate_eq_true
  unfold block199RightChunk007Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block199RightChunk007) (lo := block199RightChunk007L) (hi := block199RightChunk007R)
    (w1 := block199W1) (w2 := block199W2) (w3 := block199W3) (w4 := block199W4)
    (s1 := block199S1) (s2 := block199S2) (s3 := block199S3) (s4 := block199S4)
    hboxes hcover block199RightChunk007ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block199_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block199RightL : ℝ) (block199RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block199S1 : ℝ))
    (hy2ne : y ≠ (block199S2 : ℝ))
    (hy3ne : y ≠ (block199S3 : ℝ))
    (hy4ne : y ≠ (block199S4 : ℝ)) :
    0 < block199V y := by
  by_cases h0 : y ≤ (block199RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block199RightChunk000L : ℝ) (block199RightChunk000R : ℝ) := by
      have hL : (block199RightChunk000L : ℝ) = (block199RightL : ℝ) := by
        norm_num [block199RightChunk000L, block199RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block199_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block199RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block199RightChunk001L : ℝ) (block199RightChunk001R : ℝ) := by
        have hprev : (block199RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block199RightChunk001L : ℝ) = (block199RightChunk000R : ℝ) := by
          norm_num [block199RightChunk001L, block199RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block199_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block199RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block199RightChunk002L : ℝ) (block199RightChunk002R : ℝ) := by
          have hprev : (block199RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block199RightChunk002L : ℝ) = (block199RightChunk001R : ℝ) := by
            norm_num [block199RightChunk002L, block199RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block199_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block199RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block199RightChunk003L : ℝ) (block199RightChunk003R : ℝ) := by
            have hprev : (block199RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block199RightChunk003L : ℝ) = (block199RightChunk002R : ℝ) := by
              norm_num [block199RightChunk003L, block199RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block199_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          by_cases h4 : y ≤ (block199RightChunk004R : ℝ)
          · have hyc : y ∈ Icc (block199RightChunk004L : ℝ) (block199RightChunk004R : ℝ) := by
              have hprev : (block199RightChunk003R : ℝ) < y := lt_of_not_ge h3
              have hL : (block199RightChunk004L : ℝ) = (block199RightChunk003R : ℝ) := by
                norm_num [block199RightChunk004L, block199RightChunk003R]
              constructor
              · linarith [hprev, hL]
              · exact h4
            exact block199_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
          ·
            by_cases h5 : y ≤ (block199RightChunk005R : ℝ)
            · have hyc : y ∈ Icc (block199RightChunk005L : ℝ) (block199RightChunk005R : ℝ) := by
                have hprev : (block199RightChunk004R : ℝ) < y := lt_of_not_ge h4
                have hL : (block199RightChunk005L : ℝ) = (block199RightChunk004R : ℝ) := by
                  norm_num [block199RightChunk005L, block199RightChunk004R]
                constructor
                · linarith [hprev, hL]
                · exact h5
              exact block199_right_chunk005_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
            ·
              by_cases h6 : y ≤ (block199RightChunk006R : ℝ)
              · have hyc : y ∈ Icc (block199RightChunk006L : ℝ) (block199RightChunk006R : ℝ) := by
                  have hprev : (block199RightChunk005R : ℝ) < y := lt_of_not_ge h5
                  have hL : (block199RightChunk006L : ℝ) = (block199RightChunk005R : ℝ) := by
                    norm_num [block199RightChunk006L, block199RightChunk005R]
                  constructor
                  · linarith [hprev, hL]
                  · exact h6
                exact block199_right_chunk006_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
              ·
                have hprev : (block199RightChunk006R : ℝ) < y := lt_of_not_ge h6
                have hL : (block199RightChunk007L : ℝ) = (block199RightChunk006R : ℝ) := by
                  norm_num [block199RightChunk007L, block199RightChunk006R]
                have hR : (block199RightChunk007R : ℝ) = (block199RightR : ℝ) := by
                  norm_num [block199RightChunk007R, block199RightR]
                have hyc : y ∈ Icc (block199RightChunk007L : ℝ) (block199RightChunk007R : ℝ) := by
                  constructor
                  · linarith [hprev, hL]
                  · linarith [hy.2, hR]
                exact block199_right_chunk007_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block199_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block199LeftL : ℝ) (block199LeftR : ℝ) →
    y ≠ 0 → y ≠ (block199S1 : ℝ) → y ≠ (block199S2 : ℝ) →
    y ≠ (block199S3 : ℝ) → y ≠ (block199S4 : ℝ) → 0 < block199V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block199RightL : ℝ) (block199RightR : ℝ) →
    y ≠ 0 → y ≠ (block199S1 : ℝ) → y ≠ (block199S2 : ℝ) →
    y ≠ (block199S3 : ℝ) → y ≠ (block199S4 : ℝ) → 0 < block199V y)

theorem block199_reallog_certificate_proof :
    block199_reallog_certificate := by
  exact ⟨block199_left_V_pos, block199_right_V_pos⟩

end Block199
end M1817475
end Erdos1038Lean
