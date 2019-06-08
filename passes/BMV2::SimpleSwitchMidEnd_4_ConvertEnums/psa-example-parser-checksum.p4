--- dumps/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:34:10.562844200 +0200
+++ dumps/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-06-08 18:34:10.564821500 +0200
@@ -89,7 +89,7 @@ control ingress(inout headers hdr, inout
         meta_1.drop = true;
         ostd = meta_1;
     }
-    @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(PSA_CounterType_t.PACKETS) parser_error_counts;
+    @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(32w0) parser_error_counts;
     @name("ingress.set_error_idx") action set_error_idx_0(ErrorIndex_t idx) {
         parser_error_counts.count();
     }
