--- before_pass
+++ after_pass
@@ -89,7 +89,7 @@ control ingress(inout headers hdr, inout
         meta_1.drop = true;
         ostd = meta_1;
     }
-    @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(PSA_CounterType_t.PACKETS) parser_error_counts_0;
+    @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(32w0) parser_error_counts_0;
     @name("ingress.set_error_idx") action set_error_idx(ErrorIndex_t idx) {
         parser_error_counts_0.count();
     }
