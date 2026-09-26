package it.unisa.uniclass.conversazioni.controller;

import it.unisa.uniclass.common.Utils;
import it.unisa.uniclass.common.security.CSRF;
import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.UserDirectory; // INTERFACCIA
import jakarta.ejb.EJB;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.io.IOException;
import java.time.LocalDateTime;
import java.util.List;

@WebServlet(name = "inviaMessaggioChat", value = "/inviaMessaggioChatServlet")
public class inviaMessaggioChatServlet extends HttpServlet {

    @EJB
    private MessaggioService messaggioService;

    @EJB
    private UserDirectory userDirectory;

    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response) {
        try {
            response.sendError(HttpServletResponse.SC_METHOD_NOT_ALLOWED);
        } catch (IOException ignored) {}
    }


    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        try {
            if (!CSRF.isValid(request)) {
                response.sendError(HttpServletResponse.SC_FORBIDDEN);
                return;
            }
            HttpSession session = request.getSession();

            String emailSession = (String) session.getAttribute("utenteEmail");
            String emailDest = request.getParameter("emailInvio");
            String messaggioBody = request.getParameter("testo");

            if (!Utils.isTestoMsg(messaggioBody)) {
                response.sendError(HttpServletResponse.SC_BAD_REQUEST);
                return;
            }

            Accademico accademicoSelf = userDirectory.getAccademico(emailSession);
            Accademico accademicoDest = userDirectory.getAccademico(emailDest);

            if (accademicoSelf != null && accademicoDest != null) {
                Topic top = new Topic();
                top.setCorsoLaurea(accademicoSelf.getCorsoLaurea());
                top.setNome("VUOTO");

                Messaggio messaggio1 = new Messaggio();
                messaggio1.setAutore(accademicoSelf);
                messaggio1.setDestinatario(accademicoDest);
                messaggio1.setBody(messaggioBody);
                messaggio1.setDateTime(LocalDateTime.now());
                messaggio1.setTopic(top);

                messaggioService.aggiungiMessaggio(messaggio1);

                List<Messaggio> messaggi = messaggioService.trovaTutti();

                for (Messaggio m : messaggi) {
                    if (m.getAutore() != null) m.getAutore().getNome();
                    if (m.getDestinatario() != null) m.getDestinatario().getNome();
                    if (m.getTopic() != null) m.getTopic().getNome();
                }

                String accademicoDestUrl = java.net.URLEncoder.encode(
                        accademicoDest.getEmail(),
                        java.nio.charset.StandardCharsets.UTF_8
                );
                String accademicoSelfUrl = java.net.URLEncoder.encode(
                        accademicoSelf.getEmail(),
                        java.nio.charset.StandardCharsets.UTF_8
                );
                response.sendRedirect("chatServlet?accademico=" + accademicoDestUrl +
                        "&accademicoSelf=" + accademicoSelfUrl);
            } else {
                throw new ServletException("Errore nel recupero degli utenti per la chat.");
            }

        } catch (Exception e) {
            request.getServletContext().log("Error processing chat message", e);
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            } catch (IOException ignored) {}
        }
    }
}