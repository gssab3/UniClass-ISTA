package it.unisa.uniclass.conversazioni.controller;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UtenteService;
import jakarta.ejb.EJB;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

@WebServlet(name = "chatServlet", value = "/chatServlet")
public class chatServlet extends HttpServlet {

    @EJB
    private MessaggioService messaggioService;

    @EJB
    private UtenteService utenteService;

    @Override
    public void doGet(HttpServletRequest req, HttpServletResponse resp) {
        try {
            HttpSession session = req.getSession();

            String email = req.getParameter("accademico");
            String emailSelf = req.getParameter("accademicoSelf");

            // Recupero tramite servizio unificato
            Utente uDest = utenteService.getUtenteByEmail(email);
            Utente uSelf = utenteService.getUtenteByEmail(emailSelf);

            // Verifica che siano accademici (necessario per la chat)
            if (!(uDest instanceof Accademico) || !(uSelf instanceof Accademico)) {
                throw new ServletException("Uno degli utenti non è un Accademico abilitato alla chat.");
            }

            Accademico accademico = (Accademico) uDest;
            Accademico accademicoSelf = (Accademico) uSelf;

            // Recupero messaggi (Nota: idealmente usare un metodo specifico nel service invece di trovaTutti)
            List<Messaggio> tuttiMessaggi = messaggioService.trovaTutti();

            List<Messaggio> messaggiInviati = new ArrayList<>();
            List<Messaggio> messaggiRicevuti = new ArrayList<>();

            for(Messaggio messaggio : tuttiMessaggi) {
                // Filtro in memoria (Legacy logic preservata)
                if (messaggio.getDestinatario() != null &&
                        messaggio.getDestinatario().getMatricola().equals(accademicoSelf.getMatricola())) {
                    messaggiRicevuti.add(messaggio);
                }
                if (messaggio.getAutore() != null &&
                        messaggio.getAutore().getMatricola().equals(accademicoSelf.getMatricola())) {
                    messaggiInviati.add(messaggio);
                }
            }

            req.setAttribute("messaggigi", tuttiMessaggi);
            session.setAttribute("messaggigi", tuttiMessaggi);
            req.setAttribute("messaggiInviati", messaggiInviati);
            req.setAttribute("messaggiRicevuti", messaggiRicevuti);

            req.setAttribute("accademico", accademico);
            session.setAttribute("accademico", accademico);

            session.setAttribute("accademicoSelf", accademicoSelf);
            req.setAttribute("accdemicoSelf", accademicoSelf);

            resp.sendRedirect(req.getContextPath() + "/chat.jsp");
        } catch (Exception e) {
            req.getServletContext().log("Error processing chat request", e);
            try {
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (IOException ioException) {
                req.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }

    @Override
    public void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        doGet(req, resp);
    }
}