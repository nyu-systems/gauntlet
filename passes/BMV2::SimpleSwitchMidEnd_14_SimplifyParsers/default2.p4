--- dumps/p4_16_samples/default2.p4/pruned/default2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:29:32.832430400 +0200
+++ dumps/p4_16_samples/default2.p4/pruned/default2-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 17:29:32.838181200 +0200
@@ -5,9 +5,6 @@ header Header {
 parser p0(packet_in p, out Header h) {
     state start {
         p.extract<Header>(h);
-        transition next;
-    }
-    state next {
         transition accept;
     }
 }
