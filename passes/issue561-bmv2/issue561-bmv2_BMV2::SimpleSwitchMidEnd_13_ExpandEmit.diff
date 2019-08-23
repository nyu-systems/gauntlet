--- before_pass
+++ after_pass
@@ -297,7 +297,58 @@ control DeparserImpl(packet_out packet,
         packet.emit<ethernet_t>(hdr.ethernet);
         packet.emit<ipv4_t>(hdr.ipv4);
         packet.emit<tcp_t>(hdr.tcp);
-        packet.emit<Tcp_option_h[10]>(hdr.tcp_options_vec);
+        {
+            packet.emit<Tcp_option_end_h>(hdr.tcp_options_vec[0].end);
+            packet.emit<Tcp_option_nop_h>(hdr.tcp_options_vec[0].nop);
+            packet.emit<Tcp_option_ss_h>(hdr.tcp_options_vec[0].ss);
+            packet.emit<Tcp_option_s_h>(hdr.tcp_options_vec[0].s);
+            packet.emit<Tcp_option_sack_h>(hdr.tcp_options_vec[0].sack);
+            packet.emit<Tcp_option_end_h>(hdr.tcp_options_vec[1].end);
+            packet.emit<Tcp_option_nop_h>(hdr.tcp_options_vec[1].nop);
+            packet.emit<Tcp_option_ss_h>(hdr.tcp_options_vec[1].ss);
+            packet.emit<Tcp_option_s_h>(hdr.tcp_options_vec[1].s);
+            packet.emit<Tcp_option_sack_h>(hdr.tcp_options_vec[1].sack);
+            packet.emit<Tcp_option_end_h>(hdr.tcp_options_vec[2].end);
+            packet.emit<Tcp_option_nop_h>(hdr.tcp_options_vec[2].nop);
+            packet.emit<Tcp_option_ss_h>(hdr.tcp_options_vec[2].ss);
+            packet.emit<Tcp_option_s_h>(hdr.tcp_options_vec[2].s);
+            packet.emit<Tcp_option_sack_h>(hdr.tcp_options_vec[2].sack);
+            packet.emit<Tcp_option_end_h>(hdr.tcp_options_vec[3].end);
+            packet.emit<Tcp_option_nop_h>(hdr.tcp_options_vec[3].nop);
+            packet.emit<Tcp_option_ss_h>(hdr.tcp_options_vec[3].ss);
+            packet.emit<Tcp_option_s_h>(hdr.tcp_options_vec[3].s);
+            packet.emit<Tcp_option_sack_h>(hdr.tcp_options_vec[3].sack);
+            packet.emit<Tcp_option_end_h>(hdr.tcp_options_vec[4].end);
+            packet.emit<Tcp_option_nop_h>(hdr.tcp_options_vec[4].nop);
+            packet.emit<Tcp_option_ss_h>(hdr.tcp_options_vec[4].ss);
+            packet.emit<Tcp_option_s_h>(hdr.tcp_options_vec[4].s);
+            packet.emit<Tcp_option_sack_h>(hdr.tcp_options_vec[4].sack);
+            packet.emit<Tcp_option_end_h>(hdr.tcp_options_vec[5].end);
+            packet.emit<Tcp_option_nop_h>(hdr.tcp_options_vec[5].nop);
+            packet.emit<Tcp_option_ss_h>(hdr.tcp_options_vec[5].ss);
+            packet.emit<Tcp_option_s_h>(hdr.tcp_options_vec[5].s);
+            packet.emit<Tcp_option_sack_h>(hdr.tcp_options_vec[5].sack);
+            packet.emit<Tcp_option_end_h>(hdr.tcp_options_vec[6].end);
+            packet.emit<Tcp_option_nop_h>(hdr.tcp_options_vec[6].nop);
+            packet.emit<Tcp_option_ss_h>(hdr.tcp_options_vec[6].ss);
+            packet.emit<Tcp_option_s_h>(hdr.tcp_options_vec[6].s);
+            packet.emit<Tcp_option_sack_h>(hdr.tcp_options_vec[6].sack);
+            packet.emit<Tcp_option_end_h>(hdr.tcp_options_vec[7].end);
+            packet.emit<Tcp_option_nop_h>(hdr.tcp_options_vec[7].nop);
+            packet.emit<Tcp_option_ss_h>(hdr.tcp_options_vec[7].ss);
+            packet.emit<Tcp_option_s_h>(hdr.tcp_options_vec[7].s);
+            packet.emit<Tcp_option_sack_h>(hdr.tcp_options_vec[7].sack);
+            packet.emit<Tcp_option_end_h>(hdr.tcp_options_vec[8].end);
+            packet.emit<Tcp_option_nop_h>(hdr.tcp_options_vec[8].nop);
+            packet.emit<Tcp_option_ss_h>(hdr.tcp_options_vec[8].ss);
+            packet.emit<Tcp_option_s_h>(hdr.tcp_options_vec[8].s);
+            packet.emit<Tcp_option_sack_h>(hdr.tcp_options_vec[8].sack);
+            packet.emit<Tcp_option_end_h>(hdr.tcp_options_vec[9].end);
+            packet.emit<Tcp_option_nop_h>(hdr.tcp_options_vec[9].nop);
+            packet.emit<Tcp_option_ss_h>(hdr.tcp_options_vec[9].ss);
+            packet.emit<Tcp_option_s_h>(hdr.tcp_options_vec[9].s);
+            packet.emit<Tcp_option_sack_h>(hdr.tcp_options_vec[9].sack);
+        }
         packet.emit<Tcp_option_padding_h>(hdr.tcp_options_padding);
     }
 }
