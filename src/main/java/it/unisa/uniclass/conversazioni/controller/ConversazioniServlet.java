package it.unisa.uniclass.conversazioni.controller;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
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
    //@ spec_public
    //@ nullable
    private MessaggioService messaggioService;

    /**
     * Setter per iniettare il MessaggioService (utile per i test).
     * @param messaggioService il service da iniettare
     */
    //@ requires messaggioService != null;
    //@ ensures this.messaggioService == messaggioService;
    public void setMessaggioService(MessaggioService messaggioService) {
        this.messaggioService = messaggioService;
    }

    /**
     * Gestisce le richieste GET delegando al metodo doPost.
     * @param request la richiesta HTTP
     * @param response la risposta HTTP
     */
    //@ requires request != null;
    //@ requires response != null;
    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response) {
        doPost(request, response);
    }

    /**
     * Gestisce le richieste POST per visualizzare le conversazioni.
     * Recupera i messaggi inviati, ricevuti e gli avvisi per l'utente corrente.
     * @param request la richiesta HTTP
     * @param response la risposta HTTP
     */
    //@ requires request != null;
    //@ requires response != null;
    //@ requires request.getSession() != null;
    //@ requires request.getSession().getAttribute("utenteEmail") != null;
    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response) {
        try {
            HttpSession session = request.getSession();
            String email = session.getAttribute("utenteEmail").toString();


            AccademicoService accademicoService = new AccademicoService();
            Accademico accademicoSelf = accademicoService.trovaEmailUniClass(email);

            //Messaggi ricevuti dall'accademicoSelf
            List<Messaggio> messaggiRicevuti = messaggioService.trovaMessaggiRicevuti(email);
            //Messaggi inviati
            List<Messaggio> messaggiInviati = messaggioService.trovaMessaggiInviati(email);

            List<Messaggio> messaggi = messaggioService.trovaAvvisi();

            request.setAttribute("accademicoSelf", accademicoSelf);
            request.setAttribute("messaggiRicevuti", messaggiRicevuti);
            request.setAttribute("messaggiInviati", messaggiInviati);
            request.setAttribute("messaggi", messaggi);

            request.getRequestDispatcher("Conversazioni.jsp").forward(request, response);
        } catch (ServletException | IOException e) {
            request.getServletContext().log("Error processing conversazioni request", e);
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (IOException ioException) {
                request.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }
}
