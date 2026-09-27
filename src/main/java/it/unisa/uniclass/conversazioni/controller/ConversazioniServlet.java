package it.unisa.uniclass.conversazioni.controller;

import it.unisa.uniclass.common.security.Authorization;
import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Tipo;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.ejb.EJB;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.io.IOException;
import java.util.List;

@WebServlet(name = "ConversazioniServlet", value = "/Conversazioni")
public class ConversazioniServlet extends HttpServlet {

    @EJB
    private MessaggioService messaggioService;

    @EJB
    private UserDirectory userDirectory;

    public void mockMessaggioService(MessaggioService mock) {
        this.messaggioService = mock;
    }

    public void mockUserDirectory(UserDirectory mock) {
        this.userDirectory = mock;
    }

    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response) {
        doPost(request, response);
    }

    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response) {
        try {
            Utente current = Authorization.require(request, response, Tipo.Accademico);
            if (current == null) {
                return;
            }
            HttpSession session = request.getSession(false);
            String sessionEmail = session != null ? (String) session.getAttribute("utenteEmail") : null;
            if (sessionEmail == null || !sessionEmail.equalsIgnoreCase(current.getEmail())) {
                response.sendError(HttpServletResponse.SC_FORBIDDEN);
                return;
            }

            String email = sessionEmail;
            Accademico accademicoSelf = userDirectory.getAccademico(email);

            if (accademicoSelf != null) {
                String matricola = accademicoSelf.getMatricola();

                List<Messaggio> messaggiRicevuti = messaggioService.trovaMessaggiRicevuti(matricola);
                List<Messaggio> messaggiInviati = messaggioService.trovaMessaggiInviati(matricola);
                List<Messaggio> avvisi = messaggioService.trovaAvvisi();

                List<Messaggio> tuttiMessaggi = new java.util.ArrayList<>();
                tuttiMessaggi.addAll(messaggiRicevuti);
                tuttiMessaggi.addAll(messaggiInviati);

                // FIX: inizializzazione relazioni LAZY
                for (Messaggio m : tuttiMessaggi) {
                    if (m.getAutore() != null) m.getAutore().getNome();
                    if (m.getDestinatario() != null) m.getDestinatario().getNome();
                    if (m.getTopic() != null) m.getTopic().getNome();
                }

                request.setAttribute("accademicoSelf", accademicoSelf);
                request.setAttribute("messaggiRicevuti", messaggiRicevuti);
                request.setAttribute("messaggiInviati", messaggiInviati);
                request.setAttribute("messaggi", tuttiMessaggi);
                request.setAttribute("avvisi", avvisi);

                request.getRequestDispatcher("Conversazioni.jsp").forward(request, response);
            } else {
                response.sendError(HttpServletResponse.SC_FORBIDDEN, "Accesso consentito solo agli accademici.");
            }

        } catch (Exception e) {
            request.getServletContext().log("Error processing conversazioni request", e);
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            } catch (IOException ignored) {}
        }
    }
}
