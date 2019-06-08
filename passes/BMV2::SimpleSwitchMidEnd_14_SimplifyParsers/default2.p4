--- dumps/pruned/default2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:31:30.941219500 +0200
+++ dumps/pruned/default2-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-06-08 18:31:30.943406700 +0200
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
