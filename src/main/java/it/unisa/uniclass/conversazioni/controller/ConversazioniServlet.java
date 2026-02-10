package it.unisa.uniclass.conversazioni.controller;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UtenteService;
import jakarta.ejb.EJB;
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
    private UtenteService utenteService;

    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response) {
        doPost(request, response);
    }

    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response) {
        try {
            HttpSession session = request.getSession();
            if (session.getAttribute("utenteEmail") == null) {
                response.sendRedirect("Login.jsp");
                return;
            }

            String email = session.getAttribute("utenteEmail").toString();

            // Refactoring: Uso UtenteService invece di new AccademicoService()
            Utente u = utenteService.getUtenteByEmail(email);

            if (u instanceof Accademico) {
                Accademico accademicoSelf = (Accademico) u;
                String matricola = accademicoSelf.getMatricola();

                // Messaggi ricevuti dall'accademicoSelf
                List<Messaggio> messaggiRicevuti = messaggioService.trovaMessaggiRicevuti(matricola);
                // Messaggi inviati
                List<Messaggio> messaggiInviati = messaggioService.trovaMessaggiInviati(matricola);

                List<Messaggio> avvisi = messaggioService.trovaAvvisi();

                request.setAttribute("accademicoSelf", accademicoSelf);
                request.setAttribute("messaggiRicevuti", messaggiRicevuti);
                request.setAttribute("messaggiInviati", messaggiInviati);
                request.setAttribute("messaggi", avvisi);

                request.getRequestDispatcher("Conversazioni.jsp").forward(request, response);
            } else {
                // Gestione caso utente non accademico (es. admin puro)
                response.sendError(HttpServletResponse.SC_FORBIDDEN, "Accesso consentito solo agli accademici.");
            }

        } catch (Exception e) {
            request.getServletContext().log("Error processing conversazioni request", e);
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (IOException ioException) {
                request.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }
}