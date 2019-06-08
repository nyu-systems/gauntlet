--- dumps/pruned/default2-BMV2::SimpleSwitchMidEnd_10_StrengthReduction.p4	2019-06-08 18:31:30.932928600 +0200
+++ dumps/pruned/default2-BMV2::SimpleSwitchMidEnd_11_SimplifySelectCases.p4	2019-06-08 18:31:30.935398400 +0200
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
