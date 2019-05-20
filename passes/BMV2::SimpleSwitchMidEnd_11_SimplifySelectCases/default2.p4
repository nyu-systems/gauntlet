--- dumps/p4_16_samples/default2.p4/pruned/default2-BMV2::SimpleSwitchMidEnd_10_StrengthReduction.p4	2019-05-20 17:29:32.805235300 +0200
+++ dumps/p4_16_samples/default2.p4/pruned/default2-BMV2::SimpleSwitchMidEnd_11_SimplifySelectCases.p4	2019-05-20 17:29:32.816190700 +0200
@@ -5,10 +5,7 @@ header Header {
 parser p0(packet_in p, out Header h) {
     state start {
         p.extract<Header>(h);
-        transition select(h.data) {
-            default: next;
-            default: reject;
-        }
+        transition next;
     }
     state next {
         transition accept;
