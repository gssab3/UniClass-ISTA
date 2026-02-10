package it.unisa.uniclass.utenti.service;

import it.unisa.uniclass.common.exceptions.AuthenticationException;
import it.unisa.uniclass.common.exceptions.NotFoundUserException;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.model.Utente;
import jakarta.ejb.Local;

import java.util.List;

@Local
public interface UserDirectory {

    // --- Autenticazione e Accesso ---
    /**
     * Gestisce il login delegando al servizio sottostante.
     */
    Utente login(String email, String password) throws AuthenticationException;

    /**
     * Recupera un utente generico.
     */
    Utente getUser(String email);

    // --- Metodi specifici per Accademici (ex AccademicoService) ---

    /**
     * Recupera un accademico (con cast sicuro). Restituisce null se non è accademico.
     */
    Accademico getAccademico(String email);

    /**
     * Verifica rapida del ruolo per i permessi.
     */
    boolean isDocente(String email);
    boolean isStudente(String email);
    boolean isCoordinatore(String email);

    // --- Liste e Ricerche ---

    /**
     * Restituisce tutti gli utenti del sistema.
     */
    List<Utente> getTuttiGliUtenti();

    /**
     * Restituisce solo gli accademici di un certo ruolo (es. per popolare le liste nelle JSP).
     */
    List<Accademico> getAccademiciPerRuolo(Ruolo ruolo);

    // --- Gestione Profilo ---

    /**
     * Aggiorna i dati dell'utente.
     */
    void updateProfile(Utente utente);

    /**
     * Attiva o disattiva un account accademico.
     */
    void cambiaStatoAttivazione(String email, boolean stato);
}