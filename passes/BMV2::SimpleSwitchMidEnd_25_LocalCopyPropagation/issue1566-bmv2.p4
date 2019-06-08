--- before_pass
+++ after_pass
@@ -20,20 +20,15 @@ parser parserI(packet_in pkt, out Parsed
     }
 }
 control cIngress(inout Parsed_packet hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
-    bit<16> x;
     @name("cIngress.E.c1.stats") counter(32w65536, CounterType.packets) E_c1_stats_1;
     @name("cIngress.E.c1.stats") counter(32w65536, CounterType.packets) E_c1_stats_2;
     apply {
         hdr.ethernet.etherType = hdr.ethernet.etherType << 1;
-        x = hdr.ethernet.etherType;
-        x = x + 16w1;
-        E_c1_stats_1.count((bit<32>)x);
-        hdr.ethernet.etherType = x;
+        E_c1_stats_1.count((bit<32>)(hdr.ethernet.etherType + 16w1));
+        hdr.ethernet.etherType = hdr.ethernet.etherType + 16w1;
         hdr.ethernet.etherType = hdr.ethernet.etherType << 3;
-        x = hdr.ethernet.etherType;
-        x = x + 16w1;
-        E_c1_stats_1.count((bit<32>)x);
-        hdr.ethernet.etherType = x;
+        E_c1_stats_1.count((bit<32>)(hdr.ethernet.etherType + 16w1));
+        hdr.ethernet.etherType = hdr.ethernet.etherType + 16w1;
     }
 }
 control cEgress(inout Parsed_packet hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
