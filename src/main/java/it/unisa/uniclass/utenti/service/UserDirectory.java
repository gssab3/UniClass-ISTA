package it.unisa.uniclass.utenti.service;

import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Utente;
import jakarta.ejb.Local;

@Local
public interface UserDirectory {

    /**
     * Recupera un utente generico (per login, chat, info base).
     */
    Utente getUser(String email);

    /**
     * Recupera un accademico (per gestione corsi, libretto, ecc).
     * Restituisce null se l'utente non è un accademico.
     */
    Accademico getAccademico(String email);

    /**
     * Verifica se un utente ha un determinato ruolo (es. per permessi).
     */
    boolean isDocente(String email);
    boolean isStudente(String email);
}